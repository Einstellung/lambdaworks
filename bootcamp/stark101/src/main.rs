use lambdaworks_math::{
    field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField, traits::IsFFTField
    }, 
    polynomial::{compose, Polynomial},
};

use lambdaworks_crypto::{
    fiat_shamir::{
    default_transcript::DefaultTranscript, is_transcript::IsTranscript
    }, merkle_tree::{
    backends::types::Keccak256Backend, merkle::{self, MerkleTree}
    }
};
use std::iter::zip;
fn main() {

    // |F| = 2^192 + 1
    type F = Stark252PrimeField; 
    type FE = FieldElement<F>;
    type Merkle = MerkleTree<Keccak256Backend<F>>;
    fn fibonacci_sqr() -> Vec<FE> {
        let mut a = vec![FE::one(), FE::from(3141592)];
        let n = 2;
        while a.len() < 1023 {
            a.push(a[n-1].square() + a[n-2].square());
        }
        a
    }
    
    fn get_domain() -> Vec<FE>{
        let g = F::get_primitive_root_of_unity(10 as u64).unwrap(); 
        let G = (0..1024).into_iter().map(|i| g.pow(i as u64)).collect();
        G
    }
    
    fn get_eval_domain() -> Vec<FE> {
        let w = F::get_primitive_root_of_unity(192 as u64).unwrap(); // w is a 2^192th-primitive root, ie w is a generator of de multiplicative group of F.
        let h = F::get_primitive_root_of_unity(13 as u64).unwrap();
        let H: Vec<FE> = (0..8192).into_iter().map(|i| h.pow(i as u64)).collect();
        let eval_domain = H.into_iter().map(|x| w * x).collect();
        eval_domain  
    }
    
    // Interpolate and commit
    let f = Polynomial::interpolate(&get_domain(), &fibonacci_sqr()).expect("should interpolate");
    let eval_domain = get_eval_domain();
    let f_eval = eval_domain.clone().into_iter().map(|x| f.evaluate(&x)).collect::<Vec<_>>();

    log::info!("Merkle committing to evaluations");
    let mut transcript = DefaultTranscript::<F>::new(&[]);
    let f_merkle = MerkleTree::<Keccak256Backend<F>>::build(&f_eval);
    transcript.append_bytes(&f_merkle.root);
    let one = FE::one();
    let g = F::get_primitive_root_of_unity(10 as u64).unwrap();
    let x = Polynomial::new_monomial(one, 1);
    // polynomial contraints
    let p0 = (f.clone() - FE::one()) / (x.clone() - FE::one());
    let p1 = (f.clone() - FE::from(2338775057u64)) / (x.clone() - g.pow(1022usize));

    //let x_clone = x.clone();
    let numer_1: Polynomial<FE> = compose(&f,&(x.clone() * g.pow(2u64))); // f(g^2 x )
    //let fg2 = f.scale(&g.pow(2u64));
    // (f(g*x))^2 
    let numer_2 :Polynomial<FE> = compose(&f,&(x.clone() * g))*compose(&f,&(x.clone() * g));
    //let numer_2: Polynomial<FE> = f(x() * g).pow(2) * FieldElement::new((-1 + FieldElement::k_modulus() as i128) as usize);
    let numer_3: Polynomial<FE> = f.clone() * f;
    let numer2 = numer_1 + numer_2 + numer_3;
    let x_1024 = Polynomial::new_monomial(FE::one(), 1024) - Polynomial::new_monomial(FE::one(), 0); // X^1024 - 1
    let x_m_1021 = Polynomial::new(&[-g.pow(1021u64), FE::one()]); // X - g^1021
    let x_m_1022 = Polynomial::new(&[-g.pow(1022u64), FE::one()]); // X - g^1022
    let x_m_1023 = Polynomial::new(&[-g.pow(1023u64), FE::one()]); // X - g^1023
    let denom2 = x_1024 / (x_m_1021 * x_m_1022 * x_m_1023);

    //let denom2 = (x.power(1024usize) - 1) / ((x() - g.pow(1021)) * (x() - g.pow(1022)) * (x() - g.pow(1023)));
    let p2: Polynomial<FE> = numer2 / denom2;

    let a = transcript.sample_field_element();
    let b = transcript.sample_field_element();
    let c = transcript.sample_field_element();
    let cp = a * p0 + b * p1 + c *p2;

    // Commit on the cp
    let cp_eval = eval_domain
        .iter()
        .map(|x| cp.evaluate(x))
        .collect::<Vec<_>>();
    //let cp_eval = eval_domain.iter().map(|x| cp.evaluate(x)).collect();
    let cp_merkle = MerkleTree::<Keccak256Backend<F>>::build(&cp_eval);
    transcript.append_bytes(&cp_merkle.root);

    // FRI Commitment
    fn next_fri_domain(fri_domain: Vec<FE>) -> Vec<FE> {
        let next_domain = fri_domain.iter()
        .take(fri_domain.len() / 2)
        .map(|x| x.square())
        .collect();
        next_domain
    }

    fn next_fri_polynomial(poly: Polynomial<FE>, beta: FE) -> Polynomial<FE> {
        let odd_coef = poly.coefficients.clone().into_iter().skip(1).step_by(2).collect::<Vec<_>>();
        let even_coef = poly.coefficients.clone().into_iter().step_by(2).collect::<Vec<_>>();
        let odd_poly = Polynomial::new(&odd_coef) * beta;
        let even_poly = Polynomial::new(&even_coef);
        odd_poly + even_poly
    }

    fn next_fri_layer(domain: Vec<FE>, poly: Polynomial<FE>, beta: FE) -> (Vec<FE>, Polynomial<FE>, Vec<FE>) {
        let next_domain = next_fri_domain(domain);
        let next_poly = next_fri_polynomial(poly, beta);
        let next_layer = next_domain.iter().map(|x| next_poly.evaluate(x)).collect();
        (next_domain, next_poly, next_layer)
    }

    fn fri_commit(cp: Polynomial<FE>, domain: Vec<FE>, cp_eval: Vec<FE>, cp_merkle: MerkleTree<Keccak256Backend<F>>, channel: &mut DefaultTranscript<F>) -> 
    (Polynomial<FE>, Vec<Vec<FE>>, Vec<MerkleTree<Keccak256Backend<F>>>) {
        let mut layers: Vec<Vec<FE>> = vec![cp_eval];
        let mut merkles: Vec<MerkleTree<Keccak256Backend<F>>> = vec![cp_merkle];
        let mut actual_poly = cp;
        let mut actual_domain = domain;
        while actual_poly.degree() > 0{
            let beta = channel.sample_field_element();
            let (next_domain, next_poly, next_layer) = next_fri_layer(actual_domain, actual_poly, beta);
            actual_poly = next_poly;
            actual_domain = next_domain;
            layers.push(next_layer.clone());
            merkles.push(MerkleTree::<Keccak256Backend<F>>::build(&next_layer.clone()));
            channel.append_bytes(&merkles.last().unwrap().root);

        }
        channel.append_field_element(&actual_poly.coefficients[0]);
        (actual_poly, layers, merkles)
    }

    //Decommit
    fn decommit(idx: usize, layers: Vec<Vec<FE>>, merkles: Vec<Merkle>, channel: &mut DefaultTranscript<F>) {
        for (layer, merkle) in zip(&layers[0..layers.len()], &merkles[0..merkles.len()]){
            let idx = idx % layer.len();
            let sib_idx = (idx + (layer.len())/2 ) % layer.len();
            channel.append_field_element(&layer[idx]);
            channel.append_field_element(&layer[sib_idx]);
            let auth_path_sib = merkle.get_proof_by_pos(sib_idx).unwrap();
            let auth_path = merkle.get_proof_by_pos(idx).unwrap();

            for path in &auth_path_sib.merkle_path {
                channel.append_bytes(path);
            }
         
            for path in &auth_path.merkle_path {
                channel.append_bytes(path);
            }
         
                    }
        channel.append_field_element(&layers.last().unwrap()[0]);}
    

    fn decommit_on_query(idx:usize, channel:&mut DefaultTranscript<F>,layers:&Vec<Vec<FE>>,f_eval:&Vec<FE>,f_merkle:&Merkle,merkles:&Vec<Merkle>){
        let f_eval_len = f_eval.len();
        assert!(idx +16 < f_eval_len);
        channel.append_field_element(&f_eval[idx]);
        channel.append_field_element(&f_eval[idx+8]);
        channel.append_field_element(&f_eval[idx+16]);
        let auth_path = f_merkle.get_proof_by_pos(idx).unwrap();
        let auth_path_8 = f_merkle.get_proof_by_pos(idx+8).unwrap();
        let auth_path_16 = f_merkle.get_proof_by_pos(idx+16).unwrap();
        
        for path in &auth_path.merkle_path {
            channel.append_bytes(path);
        }
        for path in &auth_path_8.merkle_path {
            channel.append_bytes(path);
        }

        for path in &auth_path_16.merkle_path {
            channel.append_bytes(path);
        }

        decommit(idx, layers.to_vec(), merkles.to_vec(), channel);
    }


    /// Samples an integer in the range [min, max].
    fn sample_int(transcript: &mut DefaultTranscript<F>, min: usize, max: usize) -> usize {
        let bytes = transcript.sample();  // Assuming this returns a fixed-size array of bytes
        let mut num = 0usize;

        // Simple fold to convert bytes into a usize, then scale it into the range [min, max]
        for &byte in bytes.iter() {
            num = num.wrapping_mul(256).wrapping_add(byte as usize);
        }
        min + num % (max - min + 1)
    }
    fn decommit_fri(channel: &mut DefaultTranscript<F>, layers: &Vec<Vec<FE>>, f_eval: &Vec<FE>, f_merkle: &Merkle, merkles: &Vec<Merkle>) {
        for _ in 0..3 {
            let idx = sample_int(channel, 0, 8191-16);
            decommit_on_query(idx, channel, layers, f_eval, f_merkle, merkles);
        }
    }

}
