import YM.CF.Dial.Cobalt
set_option autoImplicit false
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
section mat
variable {n:Type*}[LinearOrder n][Fintype n]{P W: Op n}
lemma mull (p:Commute W P): lineOp P * quant W= quant W*lineOp P:=by
 rw [lineOp];
 have he: quant P*quant W=quant W*quant P:=by rw [←quant_mul,←quant_mul,p.eq]
 let f:= fun k=>chooseK (Fintype.card n) k P.trace • selector n k
 let s:= range (Fintype.card n +1); have hh : (∑ i∈s,f i)*quant W=quant W*∑ i∈s,f i:=by unfold f; simp_rw [mul_sum,sum_mul, Matrix.mul_smul,Matrix.smul_mul,selector_quant]
 rw [mul_assoc,hh,←mul_assoc,he,mul_assoc]
lemma linesM {V K:Op n}(h:Clad P P W V K)(p:Commute W P){C D:Op n}{c:ℂ}{q:Wave n}(g:Sea P q)(hx:filled P C=q)(hv:filled P D=q)
    (k:Complex.exp c • filled P D=filled P ((P*W*P)*C*(P*W*P)ᵀ)) : acts (quant W) q=Complex.exp c • q:=by
  have he: acts (quant P) q=q:=by nth_rw 1 [←g.1]; rw [←act_mul,line_quant h.proj,g.1];
  rw [hv] at k; rw [k,←boom h,hx];
  rw [throat,quant_mul,quant_mul,act_mul,he,show quant P*quant W=quant W*quant P by rw [← quant_mul,←quant_mul, p.eq],act_mul,he]
lemma presLine {s:ℂ}{q:Wave n}(h:IsStarProjection P)(p:Commute W P)(g:Sea P q)(v: Wave n)(l:acts (quant W) q=s • q): inner ℂ q (acts (quant W) v)=s*inner ℂ q v:=by
  have he: q≠0:=norm_pos_iff.mp (g.2.symm ▸ zero_lt_one)
  apply smul_left_injective ℂ he
  dsimp only
  rw [← Sea.scalar h g,show acts (lineOp P) (acts (quant W) v)=_ from (act_mul ..).symm,mull p,act_mul,Sea.scalar h g,map_smul,l,smul_smul,mul_comm s]
def effectK(W:Op n)(p:Wave n):=acts (quant W) p
lemma steadyK {S:ℂ}{a:Wave n}(h:effectK W a=S • a)(p:Sea P a): skyGlow a W a=S:=by
  unfold skyGlow; rw [show acts _ _=_ from h, inner_smul_right,inner_self_eq_norm_sq_to_K,p.2]; simp
lemma tailU {m: Type*}[LinearOrder m][Fintype m](H: Wave m→L[ℂ] Wave n)(Q : Wave n →L[ℂ] Wave m)(x:Wave n)(p:Wave m)(a s:ℂ)
   (h:∀ i:Wave n, inner ℂ p (Q i)=inner ℂ (H p) i) (e:x=a • H p)(g:IsStarProjection P)(hv: Sea P x)(hr: effectK W x=s • x)(hp:Commute W P)(w: Wave n)(hb:s≠0)(ht:‖a‖=1):
  inner ℂ p (((a*s)⁻¹:ℂ) • Q (effectK W w))=inner ℂ x w:=by
  have he:=presLine g hp hv w hr; rw [e,inner_smul_left,inner_smul_left] at he
  have hh:star a*a=1:= scale_unit_self ht; have hz:a≠0:=norm_pos_iff.mp (ht.symm ▸ one_pos)
  have hQ:inner ℂ (H p) (effectK W w)=s*inner ℂ (H p) w:=by
    apply mul_left_cancel₀ (show star a≠0 from star_ne_zero.mpr hz)
    change star a*_ =s*(star a*inner ℂ _ w) at he;
    exact he.trans (mul_left_comm ..)
  rw [inner_smul_right,h,hQ,e,inner_smul_left]; change _=star a* _; rw [show star a=a⁻¹ from eq_inv_of_mul_eq_one_left hh]; field_simp
end mat
variable (j:ℕ)(L:Side)(ho:Odd L.val)(hj:Even j)(he:1≤ j)(T:Script Male)(h: Use j L T)(n:ℕ)
include hj he ho h
lemma pres (p:Joy L skirt (rack T) n)(hn:0<n): Still L fun G x=>∀ M,
 let W:= ticketT T true M G (post x).1; let P:=lobe G true; let S:= Complex.exp ((earnings skirt (rack T) n M G (post x)).trace); let v:=oceanA G
 effectK W v= S • v :=by
  apply (((bonus j L ho hj he T h).taxes ho hn p).plus (spinning j L ho hj he T h)).forward
  intro N F G hc x hp i W P S v
  have hl:=hp.2 i; obtain ⟨he,hQ,h⟩:= hp.1 i -- same names shadow
  have hz:∀ u, filled (lobe G true) (squareD G u (post x))=v:=fun u=> constA G u x
  apply linesM hl.2 hl.1 (seaA G) (hz true) (hz false); rw [he]; exact hQ
omit ho h he hj
def chargeA {N F:Side}(G:Ratio N F)(i:Male)(x:Coil N F):= skyGlow (oceanA G) (ticketT T true i G x) (oceanA G)
def fire {N F: Side}(G:Ratio N F)(i:Male)(x:Coil N F)(v :Wave (Iota G)):Wave (Single N):=
 ((sect0 G * chargeA T G i x)⁻¹:ℂ) • pailL (patchQ G) (reefS G true) (effectK (ticketT T true i G x) v)
include ho he hj h
lemma lobeInvoice (p: Joy L skirt (rack T) n)(g:0<n): Still L fun G x=>∀ i,
 let W:= ticketT T true i G (post x).1
 chargeA T G i (post x).1=Complex.exp ((earnings skirt (rack T) n i G (post x)).trace)∧∀ v: Wave (Iota G), inner ℂ (mateK _) (fire T G i (post x).1 v)=inner ℂ (oceanA G) v:=by
  apply ((pres j L ho hj he T h n p g).plus (spinning j L ho hj he T h)).forward
  intro N F G he x hp i W -- named
  let y:=post x; let z:=sect0 G; let c:= Complex.exp ((earnings skirt (rack T) n i G (post x)).trace); let X:=oceanA G
  have hu:=hp.1 i; have hr: Sea (lobe G true) X:=seaA G
  have hv:chargeA T G i y.1=c:= steadyK (P:=lobe G true) (W:=W) (a:=X) hu hr
  refine ⟨hv,fun q=>?_⟩; unfold fire
  rw [show chargeA T G i _=_ from hv]; exact tailU (W:=W) _ _ X (mateK N) z c (fun i=>pails _ _ (reefS_deck ..) _ _) (sec_phase G) (lobe_sq ..) hr hu (hp.2 i).1 q (Complex.exp_ne_zero _) (sectorU G)
end YM.CF.Dial
