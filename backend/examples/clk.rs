use p3_koala_bear::KoalaBear;
use p3_uni_stark::get_symbolic_constraints;

use runwai_p3::air::RunwaiAir;
use runwai_p3::ast::Expr;

fn main() {
    let expr = Expr::from_json_file("examples/clk.json").unwrap();
    //println!("{:#?}", expr);

    let air = RunwaiAir::<KoalaBear>::new(expr, 2);
    let symbolic_constraints = get_symbolic_constraints(&air, 0, 0);
    for sc in &symbolic_constraints {
        println!("{:?}", sc);
    }
}
