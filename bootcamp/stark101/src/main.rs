use lambdaworks_math::{
    field::{
    traits::IsFFTField,
    fields::fft_friendly::stark_252_prime_field::Stark252PrimeField, 
    element::FieldElement
    }, 
    polynomial::Polynomial
};

use lambdaworks_crypto::{
    merkle_tree::{
    merkle::MerkleTree, 
    backends::types::Keccak256Backend
    },
    fiat_shamir::{
    is_transcript::IsTranscript,
    default_transcript::DefaultTranscript
    }
};

fn main() {

    // |F| = 2^192 + 1
    type F = Stark252PrimeField; 
    type FE = FieldElement<F>;

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
    let f_eval = eval_domain.iter().map(|x| f.evaluate(x));

    log::info!("Merkle committing to evaluations");
    let mut transcript = DefaultTranscript::<F>::new(&[]);
    let f_merkle = MerkleTree::<Keccak256Backend<F>>::build(&f_eval);
    transcript.append_bytes(&f_merkle.root);

    // polynomial contraints
    let p0 = (f.clone() - FE::one()) / (x() - FE::one());
    let p1 = (f.clone() - FE::new(2338775057)) / (x() - g.pow(1022usize));

    // Third polynomial contraint
    let numer_1: Polynomial = f(x() * g.pow(2));
    let numer_2: Polynomial = f(x() * g).pow(2) * FieldElement::new((-1 + FieldElement::k_modulus() as i128) as usize);
    let numer_3: Polynomial = f.pow(2) * FieldElement::new((-1 + FieldElement::k_modulus() as i128) as usize);
    let numer2: Polynomial = numer_1 + numer_2 + numer_3;
    println!("Numerator at g^1020 is {:?}", numer2.clone()(g.pow(1020)));
    println!("Numerator at g^1021 is {:?}", numer2(g.pow(1021usize)));
    let denom2 = (x().pow(1024usize) - 1) / ((x() - g.pow(1021)) * (x() - g.pow(1022)) * (x() - g.pow(1023)));
    let p2: Polynomial = numer2 / denom2;

    let a = transcript.sample_field_element();
    let b = transcript.sample_field_element();
    let c = transcript.sample_field_element();
    let cp = a * p0 + b * p1 + c *p2;

    // Commit on the cp
    let cp_eval = eval_domain.iter().map(|x| cp.evaluate(x));
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
        let odd_coef = poly.coefficients().iter().skip(1).step_by(2).collect();
        let even_coef = poly.coefficients().iter().step_by(2).collect();
        let odd_poly = Polynomial::new(&odd_coef) * beta;
        let even_poly = Polynomial::new(&even_coef);
        odd_poly + even_poly
    }

    fn next_fri_layer(domain: Vec<FE>, poly: Polynomial<FE>, beta: FE) -> (Vec<FE>, Polynomial<FE>, Vec<FE>) {
        let next_domain = next_fri_domain(domain);
        let nex_poly = next_fri_polynomial(poly, beta);
        let next_layer = next_domain.iter().map(|x| next_poly(x)).collect();
        (next_domain, next_poly, next_layer)
    }

    fn fri_commit(cp: Polynomial<FE>, domain: Vec<FE>, cp_eval: Vec<FE>, cp_merkle: MerkleTree, channel: &mut DefaultTranscript<F>) -> 
    (Polynomial<FE>, Vec<Vec<FE>>, Vec<MerkleTree>) {
        let mut layers: Vec<Vec<FE>> = vec![cp_eval];
        let mut merkles: Vec<MerkleTree> = vec![cp_merkle];
        let mut actual_poly = cp;
        let mut actual_domain = domain;
        while actual_poly.degree() > 0{
            let beta = channel.sample_field_element();
            let (next_domain, next_poly, next_layer) = next_fri_layer(actual_domain, actual_poly, beta);
            actual_poly = next_poly;
            actual_domain = next_domain;
            layers.push(next_layer);
            merkles.push(MerkleTree::<Keccak256Backend<F>>::build(&next_layer));
            channel.append_bytes(&merkles[-1]);

        }
        channel.append_bytes(actual_poly);
    }

    //Decommit
    fn decommit(idx: usize, layers: Vec<Vec<FE>>, merkles: Vec<MerkleTree>, channel: &mut DefaultTranscript<F>) {
        for (layer, merkle) in zip(layers[:layers.last()], merkles[:merkles.last()]){
            let idx = idx % layer.len();
            let sibiling_idx = (idx + (layer.len())/2 ) % layer.len();
            channel.append_bytes(layer[idx]);
            channel.append_bytes(layer[sibiling_idx]);
            channel.append_bytes(merkle.get_proof_by_pos(idx));
            channel.append_bytes(merkle.get_proof_by_pos(sibiling_idx));
        }
        channel.append_bytes(new_bytes)
    }
    }