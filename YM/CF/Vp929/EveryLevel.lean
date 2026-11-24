import YM.CF.Vp929.RateZero
import YM.CF.Continuum.Square
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade

variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
open Haro Window
open scoped ENNReal
variable {W:GivenX V U}{M:Side}{l₀ N0 B1:ℕ}{q:Chi}{J:Robes N V W}{ρ f:ℕ→ℝ}{δ C R0:ℝ→ℝ} {h:ℝ}{T:Month x 1 6 2 N0 V W} {p0:T.q ≤ M.val} {W0:Cape M B R.L} (F0:Parcel J q h δ C R0 T p0 W0 ρ f l₀)

local notation "S₀" => cell M B R.L
local notation "Xc" => F0.gram
local notation "P" => T.a
local notation "Vγ" => W.arm (T.large.trans p0) l₀
local notation "Σπ" i:max => partitionZ (F0.gram i) U (W0 i)
local notation "dX" m:max => hat R.L x m
local notation "kG" => K.top.clip
local notation "ℓ" => R.L
private lemma own_curr (i:ℕ)(t:i ≤ l₀):let G:= F0.gram i; Xc i=construct (T.a i) (V.L.path (l₀-i)) K.top.clip ((W.arm (T.large.trans p0) l₀).Q i) G.beta (G.F,G.K) G.v:=by
 intro G; let e:= F0.pull.owns i t; let g:= (F0.pull.note i t).lot_p le_rfl le_rfl; rw [show T.a i=G.p from e.width,show V.L.path _=G.path from e.path,show K.top.clip=G.funds from e.fund,show (Vγ).Q i=G.J from e.taste]; unfold construct; rw [←g.live]
private lemma pExtend(hH:1 ≤ h)(hx:1 ≤ x)(Z:CanCape J q M W0)(j:ℕ)(v:j ≤ l₀) : Envelope (denZ (F0.gram j) U (W0 j)) ∧ ∀ i, ‖field U (F0.gram j) (W0 j) i‖ ≤ Real.exp (earnings W (T.a j) (2*hat R.L x j) (dleaf R.L (hat R.L x j))*sites (cell M B R.L j)):=by
 let γ:= own_curr V F0 j v; let F:=F0.gram j; have he: Xc j=construct (T.a j) (V.L.path (l₀-j)) kG ((Vγ).Q j) F.beta (F.F,F.K) F.v:=γ
 let E:= dleaf ℓ (dX j); have hp: LotR _ h E E:= he ▸ (show LotR (Xc j) h E E from (F0.pull.note j v).lot_p le_rfl le_rfl)
 have hy:=F0.pull.sift j v; have hb:0≤ F.beta:= (by have hx:= hx.trans (crown R.L x j); unfold matchedX at hy; unfold F; linarith [hy.1,hy.2]); let C':= (Z j).paid; have C:Roof (S₀ j) J.k d J.n (W0 j):={C' with paid:=fun i=>(C'.paid i).shrink J.hr.le}; let hq:=J.gran.trans (Z j).size
 rw [he]; exact ⟨ denInt W C _ hq _ _ hp, extensive W ((Vγ).sound j) C _ hq hH _ _ hp hb hy.2⟩
variable {c:ℝ}{s:Side}
abbrev ratioField{m:Side}(X:GramM (Scree.mid m B))(A:Scree.Loom (Scree.mid m B)) (U:Grasp V.U B d):= fun i=> (partitionZ X U A)⁻¹ • denZ X U A i
private lemma mono_sites (i:ℕ) : sites (S₀ i) ≤ sites (S₀ (i+1)):=by
 unfold sites; apply pow_le_pow_left₀ (by positivity); norm_cast; change (Domain (mesh M R.L i) B).val ≤ (Domain (mesh M R.L (i+1)) B).val; rw [mesh_succ]; set v:=Vale.mesh M R.L i; change _*2*B.val*2 ≤ v.val*R.L.val*2*B.val*2; gcongr; exact Nat.le_mul_of_pos_right _ R.L.property
private def priceStep (C:ℝ→ℝ) (R:Patch) (x b:ℝ) :ℕ→ℝ
 | 0=>b
 | n+1=>priceStep C R x b n+|C (hat R.L x n)|
variable (v:ℝ)
local notation "Cs" j:max=> priceStep C R x v j
private lemma posCs (t:0 ≤ v)(j:ℕ) :0≤ priceStep C R x v j:=by induction j with | zero=> exact t | succ n ih=> exact add_nonneg ih (abs_nonneg _)
local notation "pS" m:max=> sites (cell M B R.L m)
lemma apply_level (t:0 ≤ v)(p₁:Real.exp (-v * sites (cell M B R.L 0)) ≤ ‖compensated U (F0.gram 0) (W0 0)‖) (j:ℕ)(p:j ≤ l₀) : Real.exp (-priceStep C R x v j*pS j) ≤ ‖compensated U (Xc j) (W0 j)‖:=by
 induction j with
 | zero => exact p₁
 | succ j ih=>
    have he:= ih (Nat.le_of_lt p); let V0:= pS j; let Vp:=pS (j+1); let Z:= ‖Σπ j‖; let a:= Xc j; let b:=Xc (j+1); have ht:=F0.perSite j p; change |a.v.re-b.v.re| ≤ _ at ht
    simp only [compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at *; rw [(F0.balance (j+1) p).trans (F0.balance j (le_of_lt p)).symm]; change Real.exp (- Cs (j+1)*Vp) ≤ Real.exp (- b.v.re)* Z
    let w:= Cs j; let α:= C (hat R.L x j); change Real.exp (- w*V0) ≤ Real.exp (- a.v.re)*Z at he; have hCp:0 ≤ w+|α|:=posCs v t (j+1); have hc:V0 ≤Vp:=mono_sites j; have hx:0 ≤ V0:=zero_le_one.trans (sites_pos _)
    calc _ ≤ Real.exp (- (w+|α|)*V0):= (Real.exp_monotone <| mul_le_mul_of_nonpos_left hc (neg_nonpos.mpr hCp))
         _ = Real.exp (-|α| *V0)*Real.exp (-w*V0):=by rw [←Real.exp_add]; ring_nf
         _ ≤ Real.exp (-|α| *V0)*(Real.exp (- a.v.re)*Z) := mul_le_mul_of_nonneg_left he (by positivity)
         _ ≤ _ := by
            rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_monotone; obtain q: -(|α| *V0)≤ a.v.re-b.v.re:=le_trans (neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self α) hx)) ((abs_le.mp ht).1); linarith
namespace FullBill

variable {n:Side}{X:GramM (Scree.mid n B)}{W':Scree.Loom (Scree.mid n B)}{v' t' w :ℝ}
local notation "UF"=> (ratioField V X W' U)
local notation "VF"=> volume
local notation "N"=> Scree.mid n B
local notation "hZ"=> partitionZ X U W'
structure Priced (X:GramM (Scree.mid n B))(U:Grasp V.U B d)(A:Scree.Loom (Scree.mid n B))(w v:ℝ):Prop where
 lower: Real.exp (-w*sites (Scree.mid n B)) ≤ ‖compensated U X A‖
 permits: Envelope (denZ X U A)
 valid: partitionZ X U A ≠ 0
 rate: ∀ i,‖ratioField V X A U i‖ ≤ Real.exp (v*sites (Scree.mid n B))
variable (pL:Priced V X U W' w v)
include V
lemma produced (vL:Real.exp (-w*sites (Scree.mid n B)) ≤ ‖compensated U X W'‖) (s: Envelope (denZ X U W'))(hp:∀ i, ‖field U X W' i‖ ≤ Real.exp (v'*sites (Scree.mid n B)))(hf:v'+w ≤ v) : Priced V X U W' w v:=by
 have hq:0 < ‖compensated U X W'‖:= lt_of_lt_of_le (Real.exp_pos _) vL; have ht: hZ ≠ 0:=right_ne_zero_of_mul (norm_pos_iff.mp hq)
 refine ⟨vL,s,ht,fun i=>?_⟩
 have he: UF i = (compensated U X W')⁻¹ • field U X W' i :=by unfold ratioField field compensated; rw [smul_smul]; congr 1; field_simp
 rw [he,norm_smul,norm_inv]; rw [mul_comm,←div_eq_mul_inv]; apply (div_le_iff₀ hq).mpr
 refine (hp i).trans <| le_trans ?_ (mul_le_mul_of_nonneg_left vL (by positivity)); rw [←Real.exp_add]; apply Real.exp_monotone; nlinarith [sites_pos N]
include pL
lemma charged_lp (c:ENNReal) : MemLp (ratioField V X W' U) c (city _) ∧ eLpNorm (ratioField V X W' U) c (city _) ≤ ENNReal.ofReal (Real.exp (v*sites (Scree.mid n B))):=by
 let u:= hZ; have ht: AEStronglyMeasurable UF (city _):= (pL.permits.meas.aestronglyMeasurable).const_smul u⁻¹
 have hv:eLpNorm UF c (city _) ≤ ENNReal.ofReal (Real.exp (v*sites N)):= le_trans (eLpNorm_le_of_ae_bound (Eventually.of_forall pL.rate)) (by simp)
 exact ⟨⟨ht,hv.trans_lt ENNReal.ofReal_lt_top⟩, hv⟩
lemma moment_bound (F:Window.Evaluation N)(x:0 ≤ t')(y:Continuous F)(e:∀ i, ‖F i‖ ≤ t') : Integrable (fun i=> readLinear F i (denZ X U W' i)) (city _) ∧
 ‖moment (denZ X U W') F /partitionZ X U W'‖ ≤ t'*Real.exp (v*sites (Scree.mid n B)):=by
 let K:= denZ X U W'; let τ:= Real.exp (v*sites N); refine ⟨integrable_read ?_ F y,?_⟩; exact Integrable.of_bound pL.permits.meas.aestronglyMeasurable _ (Eventually.of_forall pL.permits.cost.choose_spec)
 change ‖moment K F/hZ‖ ≤ _; rw [div_eq_mul_inv,mul_comm,←read_ket_scalar]; unfold Window.moment; refine le_trans (norm_integral_le_of_norm_le (integrable_const (t'*τ)) ?_) ?_; swap; · simp [τ]
 refine Eventually.of_forall fun i=> (norm_inner_le_norm (𝕜:=ℂ) (mateK N) (acts (F i.1) (UF i))).trans ?_; rw [(Dial.tickB _).2,one_mul]; exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul (show ‖acts (F i.1)‖ ≤t' by rw [acts, Matrix.l2_opNorm_toEuclideanCLM]; exact e _) (pL.rate _) (norm_nonneg _) x)
end FullBill

open FullBill
private theorem each_bill (t:0 ≤ v)(p₁:Real.exp (-v*pS 0) ≤ ‖compensated U (F0.gram 0) (W0 0)‖)(hH:1 ≤ h)(hx:1 ≤ x)(Z:CanCape J q M W0)(j:ℕ)(t':j≤ l₀) : Priced V (Xc j) U (W0 j) (priceStep C R x v j) (priceStep C R x v j + |earnings W (T.a j) (2*hat R.L x j) (dleaf R.L (hat R.L x j))|):= produced V _ (apply_level V F0 v t p₁ j t') (pExtend V F0 hH hx Z j t').1 (pExtend V F0 hH hx Z j t').2 (by linarith [le_abs_self (earnings W (T.a j) (2*hat R.L x j) (dleaf R.L (hat R.L x j)))])

/-- Full fixed-level corollary (same histories and ratevol_0 pivot). `FullBill.Priced` includes
 a pointwise norm bound at fixed level with the *vacuum* denominator and actual phases. See also
 `FullBill.charged_lp` and `FullBill.moment_bound`. These statements are volume exponential (in
 general they cost **more**, not less, as A increases). -/
theorem DActual.ratevol {F:(s:Side)→Scree.Loom s→Prop}{Y:Prescription R B} {d₀:ℝ} (p:DActual V W J q h δ C R0 B1 N0 Y d₀ x F)(hp:1 ≤ h) :
  ∃ T : Month x 1 6 2 N0 V W,(∃ z,Usable (D:=δ) V W J N0 z d₀ T)∧ MeterQ V 1 2 6 N0 J q h R0 δ x T ∧ 1 ≤ x ∧ ∃ M₀ : Side, ∃ k σ : ℕ → ℕ,
    let n := trunk B1 ∘ k
    let A := fun i=> rung R (M₀*N) (σ i)
    StrictMono k ∧ StrictMono n ∧ StrictMono σ ∧ StrictMono (fun i=> (A i).val) ∧
    ∃ E E' : ℕ→ℝ, 0 ≤ E ∧ 0 ≤ E' ∧ ∀ i,
      (∃ M : Side, A i=M*N ∧ J.h≤ M.val) ∧ 61 ≤ (A i).val ∧
      ∃ h' : T.q ≤ (A i).val, ∃ (W0 : Cape (A i) B R.L) (ρ : ℕ→ℝ), CanCape J q (A i) W0 ∧ (∀ j, F _ (W0 j)) ∧ (∀ j, 0 < ρ j) ∧
      ∃ X : ∀ l : ℕ, Parcel J q h δ C R0 T h' W0 ρ (commonQ R B (M₀*N)) l,
      (∀ l,(X l).Prepared Y d₀)∧
      ∀ᶠ t in atTop, ∀ j ≤ n t, FullBill.Priced V ((X (n t)).gram j) U (W0 j) (E j) (E' j) :=by
 obtain ⟨T,Hh,S,e,M,k,σ,Pz⟩:=p.earn; dsimp only at Pz; obtain ⟨A,Bz,hM,u,C',p,Q⟩:=Pz
 let E:=priceStep C R x C'; let E'(j:ℕ):= E j+|earnings W (T.a j) (2*hat R.L x j) (dleaf R.L (hat R.L x j))|
 have hP:0 ≤ E:=fun i=> posCs C' p i; refine ⟨T,Hh,S,e,M,k,σ,A,Bz,hM,u,E,E',hP,fun i=>add_nonneg (hP i) (abs_nonneg _),?_⟩
 intro i; obtain ⟨t,v,q,W0,ρ,P1,P2,P3,X,z,h⟩:=Q i
 exact ⟨t,v,q,W0,ρ,P1,P2,P3,X,z,h.mono fun i w j p₀=> each_bill V _ C' p w hp e P1 j p₀⟩
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.DActual.ratevol
#print axioms YM.CF.Py.Rate.FullBill.moment_bound
#print axioms YM.CF.Py.Rate.FullBill.charged_lp
