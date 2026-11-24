import YM.SU5.Relativistic.Rebuke

set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
local notation "Dx" i:max => hat P.R.L P.x i
local notation "Dx₀" s i => count Y s i
local notation "ρ" s:max => P.V.L.path s
open CF.Pannier.Damask
open Buffered
open Papyrus.GaugeFlux
-- new estimate for ACTUAL slate response. Orbit pays for flake affine. Reports supplied same course.
variable {h κ A:ℝ}
open CF.Papyrus.Franc
-- flexible input ANY at each configuration. no meas of decomposed terms
def WardP (s i k m:ℕ) (d D:ℝ)(F:Mark (count Y s i)):Prop:=
 let R:=gram Y s i k; let N:=count Y s i; let V:=room Y s i
 ∀ x:Orbit N,let W:= V x; let T:= spar P.K.j R.J.M W;∀ p:IsStarProjection T,∃ (L:Shaft (Single N))(b:ℝ), 0<b ∧ ‖L.sell‖ ≤ 2 ∧ ‖L.buy‖ ≤ 2 ∧
 ‖(Saber (B:=tickA N) p m).glow (F (x.1,W)) * ((b:ℂ)⁻¹ • quant L.buy)‖ * ‖(b:ℂ) • (acts (quant L.sell) (changeM P.U W R.J.M))‖ ≤ Real.exp (d+D*flakes R.p.threshold x.1)
private lemma baseSlope {n:Side} (t:ℝ)(x: Pane n) : flakes t x ≤ (6:ℝ)*(RG.flags t x).card:=by
 have h: roughness t x⊆ (RG.flags t x) ×ˢ (univ: Finset PlaqAxes):=by
    intro i p; exact mem_product.mpr ⟨(flags_spec ..).2 ⟨i,WilsonStartup.anchor_visit _, (mem_filter.mp p).2⟩,mem_univ _⟩
 unfold flakes; apply (Nat.cast_le.mpr (card_le_card h)).trans; rw [card_product,card_univ,show Fintype.card PlaqAxes=6 from by decide]; push_cast; rw [mul_comm]
variable (g: FairRoute P.P P.J P.h P.N0 Chi.canonical)
private lemma scrollFuel {n:Side} {V B:Op (Single n)}(p:IsStarProjection V)(t:IsStarProjection B)(L:Shaft (Single n))(M N:Wave (Single n))(m:ℕ)(A W:FC (Single n))(b x y:ℝ)(e:0<b)(z:0≤x)
    (h:‖(Saber (B:=B) p m).glow A*((b:ℂ)⁻¹ • quant L.buy)‖*‖(b:ℂ) • (acts (quant L.sell) M)‖≤x) (g:‖(L.foldC (Saber (B:=B) p m)).glow W‖ ≤ y)(v:Sea V M)(w:Sea B N) : ‖inner ℂ N (acts A (acts W M))‖ ≤ Real.exp (stunt m B V)*x*y:=by
 let Q:= Saber (B:=B) p m; let Vx:=acts (quant (star Q.buy)) N; have hx:‖Vx‖=Real.exp (stunt m B V):=by unfold Vx; rw [show star Q.buy=1-Comb B V m from by unfold Q Saber; simp]; exact CF.Papyrus.Franc.purse p t m N w
 let S:=L.foldC Q; let A0:=(b:ℂ); have hn:A0≠0:=Complex.ofReal_ne_zero.mpr e.ne'
 let C:= (Q.glow A)*(A0⁻¹ • quant L.buy); let X:=A0 • acts (quant L.sell) M; let E:= S.glow W; have hv:C*E=A0⁻¹ • (Q.glow A * Q.glow W * quant L.buy):=by
    have he:quant L.buy*quant L.sell=1:=by rw [←quant_mul,L.pay,quant_one]
    unfold C E S; rw [L.fold_use,show L.glow (Q.glow W)=quant L.sell*Q.glow W*quant L.buy from rfl]; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; simp only [mul_assoc]; rw [←mul_assoc (quant L.buy) (quant L.sell),he,one_mul] -- simp loop

 rw [←act_mul, Shaft.lawn Q,under (B:=B) p _ M v]; change ‖inner ℂ Vx (acts (Q.glow (A*W)) M)‖≤_
 rw [show acts (Q.glow (A*W)) M= acts (C*E) X from ?_]; swap
 · unfold X; rw [hv,map_smul,act_smul,←act_mul _ (quant L.sell),mul_assoc _ (quant L.buy),←quant_mul,L.pay,quant_one,mul_one,smul_smul,mul_inv_cancel₀ hn,one_smul, Q.glow_mult]
 rw [act_mul]; apply (norm_inner_le_norm ..).trans; rw [hx,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
 exact ((Graph.spentS _ _ _).trans (mul_le_mul_of_nonneg_left ((Graph.spentS _ _ _).trans (mul_le_mul_of_nonneg_right g (norm_nonneg _))) (norm_nonneg _))).trans (le_trans (le_of_eq (show ‖C‖ * (y*‖X‖)= (‖C‖*‖X‖)*y by ring)) (mul_le_mul_of_nonneg_right h ((norm_nonneg _).trans g)))
include g
variable {R δ:ℝ}
lemma arnica (s_ : Inflation A P)(W:CF.Papyrus.Franc.postage P.K.j R)(w':CF.Papyrus.Franc.charge R ≤ P.h)(v:0≤R)(p:P.d ≤ δ)(x:∃ N:ℕ,∀ ξ> (0:ℝ),∃ γ> (0:ℝ),∃ w:ℕ,∀ n:Side,N ≤ n.val→ _root_.YM.CF.Pannier.Chancel.Winter P.K.j δ n γ w ξ)
    (ε:ℝ)(e:0<ε):∀ᶠ m:ℕ in atTop,∀ K:ℝ,0≤K→∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s≤Y.uv k→∀ F:Mark (count Y s i),∀ d:ℝ,Envelope F → WardP Y s i k m d K F→
 ‖Buffered.Afterglow.Journey.compass Y i k s F‖ ≤ Real.exp (d+ ε*sites (count Y s i)):=by
 let r:=ε/4; have he:0<r:=by unfold r; positivity
 filter_upwards [scaleTilt Y p x r he] with m X K b
 obtain ⟨L,hL,H⟩:=X
 obtain ⟨V,hV,Q⟩:= bakeYn Y W v p x w' m r he
 let D:= K+L+V; let D':=6*D; have hp:0≤D:=by unfold D; positivity
 filter_upwards [pressed Y g s_ r he,ration Y r D' (by unfold D'; positivity) he,Q,H] with s h₀ h₁ e1 e2
 filter_upwards [e1,e2] with i t v k hk hu F d E W₀
 let X:=gram Y s i k; let N:= count Y s i; let P_:= Papyrus.Mosaic.grain (N:=More N) G🌸 X.path X.funds X.p X.beta D'
 obtain ⟨pI,pm⟩:=h₁ i k hu; let R:= room Y s i; let Z:= preGa P.V (More N) (Y.uv k-s) X.beta; let z:= seaPrec P.K.j N X.J.M; let s₁:=sites N; let cc:= Real.exp (z+d+ (r+r)*s₁); let T:= fun y: Orbit N=> letterRead (F (y.1,R y)) (Graph.recX P.U X R y)
 have hh(y:Orbit N):‖T y‖ ≤ cc * P_ y.1:=by
    let T':=spar P.K.j X.J.M (R y); let J:= Graph.past X y.1; let X':= R y; let B:=F (y.1,X'); obtain ⟨Yp,H⟩:=safety Y s i k y
    obtain ⟨t',u,a,hb,v0,e⟩:= W₀ y Yp
    unfold T; rw [Graph.porch,(letterRead _).map_smul_of_tower]; rw [norm_smul,Real.norm_of_nonneg (r:=J) (Real.exp_pos _).le]
    change J*‖inner ℂ (mateK N) (acts B (acts (Graph.mile P.K.j X R y) (changeM P.U (R y) X.J.M)))‖ ≤ _; apply le_trans (mul_le_mul_of_nonneg_left (scrollFuel Yp (plus_P _) t' _ _ _ B (Graph.mile P.K.j X R y) u _ _ a (Real.exp_pos _).le e (t k hu y Yp t' hb v0) H (tickB N)) (Real.exp_pos _).le)
    unfold cc P_ Papyrus.Mosaic.grain; rw [←Real.exp_add,←Real.exp_add,←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
    have hX:= v k hu y; unfold D' D Papyrus.Mosaic.solar; nlinarith only [hX,mul_le_mul_of_nonneg_left (baseSlope X.p.threshold y.1) hp]
 have hg: Integrable T (city N):=mark_integrable (roofage Y i s).bill E ((Marks.can_read _ _ _ _ (Y.each_level i k s hk hu)).smul (Complex.exp (-X.v)))
 let U':=prior G🌸 (More N); have hx:MeasurePreserving Prod.fst (city N) U':=measurePreserving_fst; have ha:= hx.integrable_comp_of_integrable pI
 have hf: ‖num0 P.U X R F‖≤ cc*Real.exp (r*s₁+Z):=by
    change ‖∫ i,T i∂city N‖ ≤_; apply (norm_integral_le_integral_norm ..).trans; apply le_trans (integral_mono hg.norm (ha.const_mul cc) hh); change (∫ i:Orbit N,cc*P_ i.1∂city N)≤_; rw [integral_const_mul,CF.Window.usesPrior _ pI]; exact mul_le_mul_of_nonneg_left pm (Real.exp_pos _).le
 let H_:= Real.exp (chase Y i k s-r*s₁); have he:H_≤ ‖vac0 P.U X R‖:= h₀ i k hk hu; rw [Buffered.Afterglow.Journey.compass, ← same_ratio,norm_div]; apply (div_le_iff₀ (Real.exp_pos _|>.trans_le he)).mpr; refine hf.trans ((mul_le_mul_of_nonneg_left he (Real.exp_pos _).le).trans' ?_)
 unfold H_ cc; rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; change _≤ _+(Z+z-r*s₁); unfold r; change z+d+(ε/4+ε/4)*s₁+(ε/4*s₁+Z) ≤ d+ε*s₁+(Z+z-ε/4*s₁); linarith
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.arnica
