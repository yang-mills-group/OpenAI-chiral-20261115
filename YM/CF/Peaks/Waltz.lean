import YM.CF.Peaks.Mantle
import YM.CF.Peaks.Stade
/-! Support bounds for each of the contractions of the chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable (j:ℕ)(L:Side)(ho:Odd L.val)(hj:Even j)(he:1≤j)(T: Script Male)(ht:Use j L T)(u:Bool)
def ski (c:Bool) :Script Male:=fun M N P G x=>laneP (wh j L ho c M G x) (ticketT T c M G x) (pine j L ho T c M G x)
def bulwark (u z:Bool):Script Male:=fun i N P G x=>
 let W:=ticketT T u i G x; let V:=ticketT T (!u) i G x; let B:=foal j u i G x; let H:=wh j L ho u i G x
 if z then (1-H)*(1+star (ski j L ho T u i G (icec x)))*V*B else H*(1-ski j L ho T u i G x)*W*(1-B)
def sema(z:Bool): Script Male:=fun i _ _ G x=> if z then star (bulwark j L ho T u true i G (icec x))*star (pine j L ho T (!u) i G (icec x)) else pine j L ho T u i G x *bulwark j L ho T u false i G x
include hj he ht in
lemma ski_h (c): Save L false false (ski j L ho T c):=by
  obtain ⟨h,-,q⟩:=cup j L ho hj he ht c; exact ((((Save.one _).sub q).mul h).mul (pine_funds j L ho hj he T ht c))
include hj he ht in
lemma sea_h (z): Save L true true (sema j L ho T u z):=by
  have hp:= ski_h j L ho hj he T ht u; obtain ⟨h,hx,he'⟩:=cup j L ho hj he ht u
  have hz : Save L false true (bulwark j L ho T u z):=by
    cases z
    · exact ((he'.mul ((Save.one _).sub hp)).mul h).mul ((Save.one _).sub hx)
    exact ((((Save.one _).sub he').mul ((Save.one _).plus (hp.withOpp ..))).mul (cup j L ho hj he ht (!u)).1).mul hx
  cases z
  · exact (pine_funds j L ho hj he T ht u).mul hz
  exact (hz.withOpp _ _ (bulwark j L ho T u true)).mul (Save.withOpp _ _ _ (pine_funds j L ho hj he T ht (!u))) -- tune
variable {N F:Side}(G:Ratio N F)(M:Male)(U:Nom N F)
-- Pointwise values for opposite types
lemma tv (z:Bool)(i k:Iota G): let x:=unionP U; let H:=foal j u M G x; let B:=wh j L ho u M G x; let W:=ticketT T u M G x; let V:=ticketT T (!u) M G x; let K:=pine j L ho T u M G x; let Y:=pine j L ho T (!u) M G x;
  chordP H B W V K Y (z,i) (!z,k)=(if z then sema j L ho T u z M G x i k else sema j L ho T u z M G x k i):=by
  intro x H B W V K Y
  cases z
  · change costC (star K) (B*((1-laneP B W K)*W*(1-H))) k i= (K*(B*(1-ski j L ho T u M G x)*W*(1-H))) k i; unfold costC; rw [star_star]; change _ = (K*(B*(1-laneP B W K)*W*(1-H))) k i; simp only [mul_assoc]
  change costC ((1-B)*((1+star (laneP B W K))*V*H)) (star Y) i k= (star (bulwark j L ho T u true M G (icec x))*star (pine j L ho T (!u) M G (icec x))) i k
  rw [show icec x=x from revI U]; unfold bulwark; dsimp only; rw [show icec x=x from revI U]; unfold costC; change _= (star ((1-B)*(1+star (laneP B W K))*V*H)*star Y) i k; simp only [mul_assoc]
end YM.CF.Peaks
