import Runwai.Ast

abbrev bit_value_type (ident: String): Ast.Ty := (Ast.Ty.unit.refin
                                                  (Ast.Predicate.ind
                                                    (Ast.exprEq
                                                      ((Ast.Expr.var ident).fieldExpr Ast.FieldOp.mul
                                                        ((Ast.Expr.var ident).fieldExpr
                                                          Ast.FieldOp.sub (Ast.Expr.constF 1)))
                                                      (Ast.Expr.constF 0))))

abbrev eq_mul_refinement (i₁ i₂ i₃: String): Ast.Ty := Ast.Ty.unit.refin
                        (Ast.Predicate.ind
                          (Ast.exprEq (Ast.Expr.var i₁)
                            ((Ast.Expr.var i₂).fieldExpr Ast.FieldOp.mul
                              (Ast.Expr.var i₃))))

abbrev field_lt_const (t: ℕ): Ast.Ty := (Ast.Ty.field.refin
(Ast.Predicate.dep Ast.nu ((Ast.Expr.var Ast.nu).toN.binRel Ast.RelOp.lt (Ast.Expr.constN t))))

abbrev bits_to_byte_expr (i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇: String) : Ast.Expr :=
                                      ((((((((Ast.Expr.var i₀).fieldExpr Ast.FieldOp.add
                                                                ((Ast.Expr.var i₁).fieldExpr
                                                                  Ast.FieldOp.mul (Ast.Expr.constF 2))).fieldExpr
                                                            Ast.FieldOp.add
                                                            ((Ast.Expr.var i₂).fieldExpr
                                                              Ast.FieldOp.mul (Ast.Expr.constF 4))).fieldExpr
                                                        Ast.FieldOp.add
                                                        ((Ast.Expr.var i₃).fieldExpr
                                                          Ast.FieldOp.mul (Ast.Expr.constF 8))).fieldExpr
                                                    Ast.FieldOp.add
                                                    ((Ast.Expr.var i₄).fieldExpr Ast.FieldOp.mul
                                                      (Ast.Expr.constF 16))).fieldExpr
                                                Ast.FieldOp.add
                                                ((Ast.Expr.var i₅).fieldExpr Ast.FieldOp.mul
                                                  (Ast.Expr.constF 32))).fieldExpr
                                            Ast.FieldOp.add
                                            ((Ast.Expr.var i₆).fieldExpr Ast.FieldOp.mul
                                              (Ast.Expr.constF 64))).fieldExpr
                                        Ast.FieldOp.add
                                        ((Ast.Expr.var i₇).fieldExpr Ast.FieldOp.mul
                                          (Ast.Expr.constF 128)))
