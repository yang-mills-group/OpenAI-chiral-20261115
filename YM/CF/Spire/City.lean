import YM.CF.Spire.Siren
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {L m A B : Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e:ℝ} {P: Grasp Y B e}
variable (G:Ratio (CSide m B) (CSide A B))(h:G.count=L)(k:P.roundZ ≤(CSide m B).val)
lemma stemN(M:Tulip.Male)(x:Skin m B): ‖Complex.exp (candle m B (P.cost m M) x)‖=1:=by rw [Complex.norm_exp,candleN,Real.exp_zero]
lemma negC(M:Tulip.Male)(x:Skin m B): ‖Complex.exp (-candle m B (P.cost m M) x)‖=1:=by rw [Complex.exp_neg,norm_inv,stemN,inv_one]
private lemma moss_c {z:ℂ}(h:z.re=0) : star (Complex.exp (-z))=Complex.exp z:=by change cSignX true _=_; rw [← cSexp true]; congr 1; apply Complex.ext <;> simp [cSignX,h]
  
def graft (P:Grasp Y B e)(x:Skin A B)(M:Tulip.Male):=cartsL (switchG G).symm (changeM P x M)
def seedG (P:Grasp Y B e)(x:Skin m B)(M:Tulip.Male):=hoist (patchQ G) (reefS G true) (changeM P x M)
lemma graft_v(x:Skin A B)(M:Tulip.Male): graft G P x M = Complex.exp (-candle A B (P.cost A M) x) • adjust P G x M :=by rw [graft,changeM,carts_s]; rfl
lemma seedG_v(x:Skin m B)(M:Tulip.Male): seedG G P x M= Complex.exp (-candle m B (P.cost m M) x) • sear P G x M:=by rw [seedG,changeM,map_smul]; rfl
include k
lemma sea_g(u:Skin m B)(s:Guard u e)(M:Tulip.Male): Sea (spar j M u) (changeM P u M):=by have he:=heartS P.topB P.baseY.1 (P.couture k M) u s ((P.broadness _ k M).projection _ s); unfold Sea changeM; rw [map_smul,norm_smul,negC]; rw [he.1,he.2,one_mul]; exact ⟨rfl,rfl⟩ -- tune k not included
variable (x:nomA m A B)(g:JointB G x e)(l:0<e)(M:Tulip.Male)
include g k h l
lemma charter : Complex.exp (altar G P x M)=(sect0 G * chargeA (Thread j) G M (unionP x))⁻¹ * skyGlow (seedG G P x.2 (upMale L o M)) (ticketT (Thread j) true M G (unionP x)) (graft G P x.1 M):=by
 rw [altar, Complex.exp_sub, Complex.exp_add,chargeR P l G h k x g M, graft_v, seedG_v, skyGlow, skyGlow,map_smul,inner_smul_left,inner_smul_right]; rw [show ∀ z:ℂ, (starRingEnd ℂ) z=star z from (fun _=>rfl), moss_c (candleN ..),Complex.exp_neg]; ring
lemma shuttle : let u:=unionP x; let V:=Thread j; let X:= foal j true M G u; let H:=wh j L o true M G u; let W:=ticketT V true M G u; let v:=ticketT V false M G u; let K:=pine j L o V true M G u; let S:=pine j L o V false M G u;
 proxyZ (reefS G true) (patchQ G) (graft G P x.1 M) (changeM P x.2 (upMale L o M)) X H K S W v ((sect0 G * chargeA V G M u)⁻¹) (Complex.exp (altar G P x M)) ∧ ∀ y, inner ℂ (mateK (CSide m B)) (fire V G M u y)=inner ℂ (oceanA G) y:=by
 intro u V X H W v K S; have hh:= l
 obtain ⟨t,hx⟩:=cue_from x.2; let Z:=starfish m B x.2 t; let z:=accordL G x Z; have hv:=pose_g P l G h k x g Z (starK P.capY l.le g.cg hx)
 let T:= Y.cap G h (P.needed.trans k) M z hv.glyph
 have hz:= court G _ _ o _ false _ (T.chart false)
 rw [show Bool.false=(!true) from rfl,wh_neg,foil_neg] at hz
 refine ⟨project_l _ _ ?_ T.projN (court _ _ _ _ _ _ _ (T.chart true)) hz (reefS_deck ..) _ ?_ _ (sea_g k x.2 g.cg _) _ _ (charter G h k x g l M),T.fired⟩
 · exact pierce ..
 exact carts_sea (switchG G).symm T.projP (sea_g (P.clock_fine G k) x.1 g.fg _)
end YM.CF.Spire
