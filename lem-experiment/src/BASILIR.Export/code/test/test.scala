object Test {

abstract sealed class expr
final case class bvexpra() extends expr
final case class boolexpra() extends expr

def equal_expra(x0 : expr, x1 : expr) : Boolean = (x0, x1) match {
  case (bvexpra(), boolexpra()) => false
  case (boolexpra(), bvexpra()) => false
  case (boolexpra(), boolexpra()) => true
  case (bvexpra(), bvexpra()) => true
}

trait equal[A] {
  val `Test.equal` : (A, A) => Boolean
}
def equal[A](a : A, b : A)(implicit A: equal[A]) : Boolean =
  A.`Test.equal`(a, b)
object equal {
  implicit def `Test.equal_char` : equal[char] = new equal[char] {
    val `Test.equal` = (a : char, b : char) => equal_chara(a, b)
  }
  implicit def `Test.equal_expr` : equal[expr] = new equal[expr] {
    val `Test.equal` = (a : expr, b : expr) => equal_expra(a, b)
  }
}

def equal_bool(p : Boolean, pa : Boolean) : Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

abstract sealed class char
final case class Char(a : Boolean, b : Boolean, c : Boolean, d : Boolean,
                       e : Boolean, f : Boolean, g : Boolean, h : Boolean)
  extends char

def equal_chara(x0 : char, x1 : char) : Boolean = (x0, x1) match {
  case (Char(x1, x2, x3, x4, x5, x6, x7, x8),
         Char(y1, y2, y3, y4, y5, y6, y7, y8))
    => equal_bool(x1, y1) &&
         (equal_bool(x2, y2) &&
           (equal_bool(x3, y3) &&
             (equal_bool(x4, y4) &&
               (equal_bool(x5, y5) &&
                 (equal_bool(x6, y6) &&
                   (equal_bool(x7, y7) && equal_bool(x8, y8)))))))
}

abstract sealed class num
final case class One() extends num
final case class Bit0(a : num) extends num
final case class Bit1(a : num) extends num

abstract sealed class int
final case class zero_int() extends int
final case class Pos(a : num) extends int
final case class Neg(a : num) extends int

abstract sealed class BVOp
final case class BVADD() extends BVOp
final case class BVAND() extends BVOp
final case class BVOR() extends BVOp
final case class BVXOR() extends BVOp
final case class BVSDIV() extends BVOp
final case class BVUDIV() extends BVOp
final case class BVSREM() extends BVOp
final case class BVUREM() extends BVOp
final case class BVSMOD() extends BVOp
final case class BVMUL() extends BVOp
final case class BVASHR() extends BVOp
final case class BVLSHR() extends BVOp
final case class BVSHL() extends BVOp

abstract sealed class bvexpr
final case class BVConstant(a : int, b : int) extends bvexpr
final case class BinExpr(a : BVOp, b : int, c : bvexpr, d : bvexpr) extends
  bvexpr
final case class BVNot(a : int, b : bvexpr) extends bvexpr
final case class BVNeg(a : int, b : bvexpr) extends bvexpr
final case class BVVar(a : int, b : List[char]) extends bvexpr
final case class Extend(a : int, b : bvexpr) extends bvexpr
final case class BVFApply(a : List[char], b : List[expr], c : int) extends
  bvexpr

abstract sealed class boolexpr
final case class BoolConstant(a : Boolean) extends boolexpr
final case class BVCOMP(a : bvexpr, b : bvexpr) extends boolexpr
final case class BVULT(a : bvexpr, b : bvexpr) extends boolexpr
final case class BVSLT(a : bvexpr, b : bvexpr) extends boolexpr
final case class BVEQ(a : bvexpr, b : bvexpr) extends boolexpr
final case class BoolEQ(a : boolexpr, b : boolexpr) extends boolexpr
final case class BoolAND(a : boolexpr, b : boolexpr) extends boolexpr
final case class BoolOR(a : boolexpr, b : boolexpr) extends boolexpr
final case class BoolNOT(a : boolexpr) extends boolexpr
final case class BoolVar(a : List[char]) extends boolexpr
final case class BoolFApply(a : List[char], b : List[expr]) extends boolexpr

def eq[A : equal](a : A, b : A) : Boolean = equal[A](a, b)

def equal_BVOp(x0 : BVOp, x1 : BVOp) : Boolean = (x0, x1) match {
  case (BVLSHR(), BVSHL()) => false
  case (BVSHL(), BVLSHR()) => false
  case (BVASHR(), BVSHL()) => false
  case (BVSHL(), BVASHR()) => false
  case (BVASHR(), BVLSHR()) => false
  case (BVLSHR(), BVASHR()) => false
  case (BVMUL(), BVSHL()) => false
  case (BVSHL(), BVMUL()) => false
  case (BVMUL(), BVLSHR()) => false
  case (BVLSHR(), BVMUL()) => false
  case (BVMUL(), BVASHR()) => false
  case (BVASHR(), BVMUL()) => false
  case (BVSMOD(), BVSHL()) => false
  case (BVSHL(), BVSMOD()) => false
  case (BVSMOD(), BVLSHR()) => false
  case (BVLSHR(), BVSMOD()) => false
  case (BVSMOD(), BVASHR()) => false
  case (BVASHR(), BVSMOD()) => false
  case (BVSMOD(), BVMUL()) => false
  case (BVMUL(), BVSMOD()) => false
  case (BVUREM(), BVSHL()) => false
  case (BVSHL(), BVUREM()) => false
  case (BVUREM(), BVLSHR()) => false
  case (BVLSHR(), BVUREM()) => false
  case (BVUREM(), BVASHR()) => false
  case (BVASHR(), BVUREM()) => false
  case (BVUREM(), BVMUL()) => false
  case (BVMUL(), BVUREM()) => false
  case (BVUREM(), BVSMOD()) => false
  case (BVSMOD(), BVUREM()) => false
  case (BVSREM(), BVSHL()) => false
  case (BVSHL(), BVSREM()) => false
  case (BVSREM(), BVLSHR()) => false
  case (BVLSHR(), BVSREM()) => false
  case (BVSREM(), BVASHR()) => false
  case (BVASHR(), BVSREM()) => false
  case (BVSREM(), BVMUL()) => false
  case (BVMUL(), BVSREM()) => false
  case (BVSREM(), BVSMOD()) => false
  case (BVSMOD(), BVSREM()) => false
  case (BVSREM(), BVUREM()) => false
  case (BVUREM(), BVSREM()) => false
  case (BVUDIV(), BVSHL()) => false
  case (BVSHL(), BVUDIV()) => false
  case (BVUDIV(), BVLSHR()) => false
  case (BVLSHR(), BVUDIV()) => false
  case (BVUDIV(), BVASHR()) => false
  case (BVASHR(), BVUDIV()) => false
  case (BVUDIV(), BVMUL()) => false
  case (BVMUL(), BVUDIV()) => false
  case (BVUDIV(), BVSMOD()) => false
  case (BVSMOD(), BVUDIV()) => false
  case (BVUDIV(), BVUREM()) => false
  case (BVUREM(), BVUDIV()) => false
  case (BVUDIV(), BVSREM()) => false
  case (BVSREM(), BVUDIV()) => false
  case (BVSDIV(), BVSHL()) => false
  case (BVSHL(), BVSDIV()) => false
  case (BVSDIV(), BVLSHR()) => false
  case (BVLSHR(), BVSDIV()) => false
  case (BVSDIV(), BVASHR()) => false
  case (BVASHR(), BVSDIV()) => false
  case (BVSDIV(), BVMUL()) => false
  case (BVMUL(), BVSDIV()) => false
  case (BVSDIV(), BVSMOD()) => false
  case (BVSMOD(), BVSDIV()) => false
  case (BVSDIV(), BVUREM()) => false
  case (BVUREM(), BVSDIV()) => false
  case (BVSDIV(), BVSREM()) => false
  case (BVSREM(), BVSDIV()) => false
  case (BVSDIV(), BVUDIV()) => false
  case (BVUDIV(), BVSDIV()) => false
  case (BVXOR(), BVSHL()) => false
  case (BVSHL(), BVXOR()) => false
  case (BVXOR(), BVLSHR()) => false
  case (BVLSHR(), BVXOR()) => false
  case (BVXOR(), BVASHR()) => false
  case (BVASHR(), BVXOR()) => false
  case (BVXOR(), BVMUL()) => false
  case (BVMUL(), BVXOR()) => false
  case (BVXOR(), BVSMOD()) => false
  case (BVSMOD(), BVXOR()) => false
  case (BVXOR(), BVUREM()) => false
  case (BVUREM(), BVXOR()) => false
  case (BVXOR(), BVSREM()) => false
  case (BVSREM(), BVXOR()) => false
  case (BVXOR(), BVUDIV()) => false
  case (BVUDIV(), BVXOR()) => false
  case (BVXOR(), BVSDIV()) => false
  case (BVSDIV(), BVXOR()) => false
  case (BVOR(), BVSHL()) => false
  case (BVSHL(), BVOR()) => false
  case (BVOR(), BVLSHR()) => false
  case (BVLSHR(), BVOR()) => false
  case (BVOR(), BVASHR()) => false
  case (BVASHR(), BVOR()) => false
  case (BVOR(), BVMUL()) => false
  case (BVMUL(), BVOR()) => false
  case (BVOR(), BVSMOD()) => false
  case (BVSMOD(), BVOR()) => false
  case (BVOR(), BVUREM()) => false
  case (BVUREM(), BVOR()) => false
  case (BVOR(), BVSREM()) => false
  case (BVSREM(), BVOR()) => false
  case (BVOR(), BVUDIV()) => false
  case (BVUDIV(), BVOR()) => false
  case (BVOR(), BVSDIV()) => false
  case (BVSDIV(), BVOR()) => false
  case (BVOR(), BVXOR()) => false
  case (BVXOR(), BVOR()) => false
  case (BVAND(), BVSHL()) => false
  case (BVSHL(), BVAND()) => false
  case (BVAND(), BVLSHR()) => false
  case (BVLSHR(), BVAND()) => false
  case (BVAND(), BVASHR()) => false
  case (BVASHR(), BVAND()) => false
  case (BVAND(), BVMUL()) => false
  case (BVMUL(), BVAND()) => false
  case (BVAND(), BVSMOD()) => false
  case (BVSMOD(), BVAND()) => false
  case (BVAND(), BVUREM()) => false
  case (BVUREM(), BVAND()) => false
  case (BVAND(), BVSREM()) => false
  case (BVSREM(), BVAND()) => false
  case (BVAND(), BVUDIV()) => false
  case (BVUDIV(), BVAND()) => false
  case (BVAND(), BVSDIV()) => false
  case (BVSDIV(), BVAND()) => false
  case (BVAND(), BVXOR()) => false
  case (BVXOR(), BVAND()) => false
  case (BVAND(), BVOR()) => false
  case (BVOR(), BVAND()) => false
  case (BVADD(), BVSHL()) => false
  case (BVSHL(), BVADD()) => false
  case (BVADD(), BVLSHR()) => false
  case (BVLSHR(), BVADD()) => false
  case (BVADD(), BVASHR()) => false
  case (BVASHR(), BVADD()) => false
  case (BVADD(), BVMUL()) => false
  case (BVMUL(), BVADD()) => false
  case (BVADD(), BVSMOD()) => false
  case (BVSMOD(), BVADD()) => false
  case (BVADD(), BVUREM()) => false
  case (BVUREM(), BVADD()) => false
  case (BVADD(), BVSREM()) => false
  case (BVSREM(), BVADD()) => false
  case (BVADD(), BVUDIV()) => false
  case (BVUDIV(), BVADD()) => false
  case (BVADD(), BVSDIV()) => false
  case (BVSDIV(), BVADD()) => false
  case (BVADD(), BVXOR()) => false
  case (BVXOR(), BVADD()) => false
  case (BVADD(), BVOR()) => false
  case (BVOR(), BVADD()) => false
  case (BVADD(), BVAND()) => false
  case (BVAND(), BVADD()) => false
  case (BVSHL(), BVSHL()) => true
  case (BVLSHR(), BVLSHR()) => true
  case (BVASHR(), BVASHR()) => true
  case (BVMUL(), BVMUL()) => true
  case (BVSMOD(), BVSMOD()) => true
  case (BVUREM(), BVUREM()) => true
  case (BVSREM(), BVSREM()) => true
  case (BVUDIV(), BVUDIV()) => true
  case (BVSDIV(), BVSDIV()) => true
  case (BVXOR(), BVXOR()) => true
  case (BVOR(), BVOR()) => true
  case (BVAND(), BVAND()) => true
  case (BVADD(), BVADD()) => true
}

def equal_list[A : equal](x0 : List[A], x1 : List[A]) : Boolean = (x0, x1)
  match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) => eq[A](x21, y21) && equal_list[A](x22, y22)
  case (Nil, Nil) => true
}

def equal_num(x0 : num, x1 : num) : Boolean = (x0, x1) match {
  case (Bit0(x2), Bit1(x3)) => false
  case (Bit1(x3), Bit0(x2)) => false
  case (One(), Bit1(x3)) => false
  case (Bit1(x3), One()) => false
  case (One(), Bit0(x2)) => false
  case (Bit0(x2), One()) => false
  case (Bit1(x3), Bit1(y3)) => equal_num(x3, y3)
  case (Bit0(x2), Bit0(y2)) => equal_num(x2, y2)
  case (One(), One()) => true
}

def equal_int(x0 : int, x1 : int) : Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => equal_num(k, l)
  case (Neg(k), Pos(l)) => false
  case (Neg(k), zero_int()) => false
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => equal_num(k, l)
  case (Pos(k), zero_int()) => false
  case (zero_int(), Neg(l)) => false
  case (zero_int(), Pos(l)) => false
  case (zero_int(), zero_int()) => true
}

def equal_bvexpr(x0 : bvexpr, x1 : bvexpr) : Boolean = (x0, x1) match {
  case (Extend(x61, x62), BVFApply(x71, x72, x73)) => false
  case (BVFApply(x71, x72, x73), Extend(x61, x62)) => false
  case (BVVar(x51, x52), BVFApply(x71, x72, x73)) => false
  case (BVFApply(x71, x72, x73), BVVar(x51, x52)) => false
  case (BVVar(x51, x52), Extend(x61, x62)) => false
  case (Extend(x61, x62), BVVar(x51, x52)) => false
  case (BVNeg(x41, x42), BVFApply(x71, x72, x73)) => false
  case (BVFApply(x71, x72, x73), BVNeg(x41, x42)) => false
  case (BVNeg(x41, x42), Extend(x61, x62)) => false
  case (Extend(x61, x62), BVNeg(x41, x42)) => false
  case (BVNeg(x41, x42), BVVar(x51, x52)) => false
  case (BVVar(x51, x52), BVNeg(x41, x42)) => false
  case (BVNot(x31, x32), BVFApply(x71, x72, x73)) => false
  case (BVFApply(x71, x72, x73), BVNot(x31, x32)) => false
  case (BVNot(x31, x32), Extend(x61, x62)) => false
  case (Extend(x61, x62), BVNot(x31, x32)) => false
  case (BVNot(x31, x32), BVVar(x51, x52)) => false
  case (BVVar(x51, x52), BVNot(x31, x32)) => false
  case (BVNot(x31, x32), BVNeg(x41, x42)) => false
  case (BVNeg(x41, x42), BVNot(x31, x32)) => false
  case (BinExpr(x21, x22, x23, x24), BVFApply(x71, x72, x73)) => false
  case (BVFApply(x71, x72, x73), BinExpr(x21, x22, x23, x24)) => false
  case (BinExpr(x21, x22, x23, x24), Extend(x61, x62)) => false
  case (Extend(x61, x62), BinExpr(x21, x22, x23, x24)) => false
  case (BinExpr(x21, x22, x23, x24), BVVar(x51, x52)) => false
  case (BVVar(x51, x52), BinExpr(x21, x22, x23, x24)) => false
  case (BinExpr(x21, x22, x23, x24), BVNeg(x41, x42)) => false
  case (BVNeg(x41, x42), BinExpr(x21, x22, x23, x24)) => false
  case (BinExpr(x21, x22, x23, x24), BVNot(x31, x32)) => false
  case (BVNot(x31, x32), BinExpr(x21, x22, x23, x24)) => false
  case (BVConstant(x11, x12), BVFApply(x71, x72, x73)) => false
  case (BVFApply(x71, x72, x73), BVConstant(x11, x12)) => false
  case (BVConstant(x11, x12), Extend(x61, x62)) => false
  case (Extend(x61, x62), BVConstant(x11, x12)) => false
  case (BVConstant(x11, x12), BVVar(x51, x52)) => false
  case (BVVar(x51, x52), BVConstant(x11, x12)) => false
  case (BVConstant(x11, x12), BVNeg(x41, x42)) => false
  case (BVNeg(x41, x42), BVConstant(x11, x12)) => false
  case (BVConstant(x11, x12), BVNot(x31, x32)) => false
  case (BVNot(x31, x32), BVConstant(x11, x12)) => false
  case (BVConstant(x11, x12), BinExpr(x21, x22, x23, x24)) => false
  case (BinExpr(x21, x22, x23, x24), BVConstant(x11, x12)) => false
  case (BVFApply(x71, x72, x73), BVFApply(y71, y72, y73)) =>
    equal_list[char](x71, y71) &&
      (equal_list[expr](x72, y72) && equal_int(x73, y73))
  case (Extend(x61, x62), Extend(y61, y62)) =>
    equal_int(x61, y61) && equal_bvexpr(x62, y62)
  case (BVVar(x51, x52), BVVar(y51, y52)) =>
    equal_int(x51, y51) && equal_list[char](x52, y52)
  case (BVNeg(x41, x42), BVNeg(y41, y42)) =>
    equal_int(x41, y41) && equal_bvexpr(x42, y42)
  case (BVNot(x31, x32), BVNot(y31, y32)) =>
    equal_int(x31, y31) && equal_bvexpr(x32, y32)
  case (BinExpr(x21, x22, x23, x24), BinExpr(y21, y22, y23, y24)) =>
    equal_BVOp(x21, y21) &&
      (equal_int(x22, y22) &&
        (equal_bvexpr(x23, y23) && equal_bvexpr(x24, y24)))
  case (BVConstant(x11, x12), BVConstant(y11, y12)) =>
    equal_int(x11, y11) && equal_int(x12, y12)
}

def evalbool(x0 : boolexpr) : Boolean = x0 match {
  case BoolConstant(b) => b
  case BVCOMP(e1, e2) => ! (equal_bvexpr(e1, e2))
  case BVULT(v, va) => false
  case BVSLT(v, va) => false
  case BVEQ(v, va) => false
  case BoolEQ(v, va) => false
  case BoolAND(v, va) => false
  case BoolOR(v, va) => false
  case BoolNOT(v) => false
  case BoolVar(v) => false
  case BoolFApply(v, va) => false
}

} /* object Test */
