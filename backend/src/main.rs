use runwai_p3::ast::Expr;

fn main() {
    let expr = Expr::from_json_file("expr.json").unwrap();
    println!("{:#?}", expr);
}
