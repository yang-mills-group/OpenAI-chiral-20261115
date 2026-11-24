import YM.SU5.WakeInvestment.BookBill
import YM.SU5.WakeInvestment.Range
import YM.SU5.WakeInvestment.Pillow
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph

variable {z A c:ℝ}
local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "shx" s:max => hat L P.x s
local notation "vℓ" s:max => shieldC (hat L P.x s)
local notation "Ω" s:max i:max => (side Y i s)
local notation "Gξ" s:max i:max k:max => RootBook Y i k s
local notation "ℂk" s:max i:max => (Y.voyage i).CapeT s

open WakeInvestment
local notation "ℰ" s:max => Worth.meterC (shx s)


variable (s i k : ℕ)
local notation "flatP" => spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
local notation "N" s:max i:max => side Y i s
local notation "ηP" s:max => Worth.gateC (shx s)
local notation "ptQ" s:max i:max k:max => ((RootBook Y i k s).p)
open Rous

/-- True Pole. WA.2 before courier. Use the calibrated Grasp, even at these
finite i,k, not a chosen canonical phase from the flat proof. -/
def flatSea : Wave (Single (side Y i s)) := changeM P.U (1:Pane (side Y i s)) (RootBook Y i k s).J.M

lemma preparedFlat : Sea flatP (flatSea Y s i k) := by
  exact Spire.sea_g (P.J.gran.trans ((Y.voyage i).ownership s).size) _ (guard0 P.dpos.le) _

-- precise sign & phase, ready to invoke against each rotated polynomial
def noble (F : FC (Single (side Y i s))) : ℂ :=
    inner ℂ (mateK (side Y i s)) (acts F (flatSea Y s i k)) / inner ℂ (mateK (side Y i s)) (flatSea Y s i k)

lemma onTicket (F : FC (Single (side Y i s))) : noble Y s i k F= WakeInvestment.grain (flatSea Y s i k) ((flatShear Y s i k).glow F) :=
    (wick_prepayment (nontrivial_spin P) (flat_post Y s i k) (mateK _) (flatSea Y s i k) (tickB _) (preparedFlat Y s i k) F).symm

def movedRoot (x : Orbit (side Y i s)) (F : FC (Single (side Y i s))) := (unitStem (tradew _ (atFrame Y s i x))).glow F

lemma moved_root (x : Orbit (side Y i s)) (F : FC (Single (side Y i s))) :
    movedRoot Y s i x F= twist (quantU (tradew _ (atFrame Y s i x))) F := by rw [twist_formula]; unfold movedRoot unitStem Shaft.glow; simp only [quant_star]; rfl

-- public term. W are pre-root-cost (no unit yet), issued Mark roots
variable {n_ m:ℕ}
def fullRead (Y : Course P (VolumeCape.Dream.Nimbus ℓ)) (s i:ℕ) (F:Fin n_→ Mark (side Y i s)) : Mark (side Y i s):= (List.ofFn fun j => 1+F j).prod

lemma release(T: Shaft (Single (side Y i s))) (X:Fields (side Y i s))(F:Fin n_→ Mark (side Y i s)) :
    T.glow (fullRead Y s i F X)=stripTil (T.glow ∘ (fun j:Fin n_=> F j X)) 1:= by
  induction n_ with
  | zero=> unfold fullRead stripTil; simp [T.glow_nil]
  | succ n ih=>
               rw [fullRead,stripTil,List.ofFn_succ,List.ofFn_succ,List.prod_cons,List.prod_cons,Pi.mul_apply,Pi.add_apply,T.glow_mult,T.glow_sum]; let G : Fin n → Mark (side Y i s) :=fun j=> F j.succ
               change (T.glow 1+T.glow (F 0 X))*T.glow (fullRead Y s i G X)=_ ; rw [ih,T.glow_nil]; change _=(1+(1:ℝ) • (T.glow (F 0 X)))*_; rw [one_smul]; rfl

abbrev flatSeat (A:Fin n_→ Mark (side Y i s)) (j:Fin n_)(x:Orbit (side Y i s)) := movedRoot Y s i x (A j (x.1,(Y.voyage i).CapeT s x))

/-- Checker row **leading price**: carries the real part through the integral. This is a
fiber-on-configuration estimate; allow arbitrary *leading* use on the orbit (e.g. with an
exception/covariance pupil penalty in that price). Q typically partial projection error for spinning
fields. Must still bound exponential moments against gauge comparison (in `actor_axis`).
-/
structure Fitting (K B e : ℝ)(m:ℕ) (F:Fin n_→ Mark (side Y i s)) (x:Orbit (side Y i s)) : Prop where
  pose : ∃ σ: Fin n_→ Finset (Single (side Y i s)), Set.PairwiseDisjoint Set.univ σ ∧
    ∃ (G:Fin n_→FC (Single (side Y i s)))(δ:Fin n_→ℝ), (∀ i,Lyrics (σ i) m K (G i)) ∧
    (∀ j t, 0 ≤ t→t ≤1→
       let W:= weighted flatP t (flatShear Y s i k)
       let f':= W.glow (flatSeat Y s i F j x)
       ‖f'- W.glow (G j)‖ ≤ δ j ∧ ‖f'‖ ≤ B) ∧
    ∑ j, ((noble Y s i k (G j)).re+δ j) ≤ e
  comm : ∀ p q, Commute (F p (x.1, (Y.voyage i).CapeT s x)) (F q (x.1, (Y.voyage i).CapeT s x))

variable {K β V w c ε μ E B : ℝ}{Ξ:Shaft (Single (side Y i s))}{F: Fin n_→ Mark (side Y i s)}
lemma Fitting.held (x:Orbit (side Y i s))(A:Fitting Y s i k K B c m F x)
    (nK:0≤ K) (r: Pillow (flatShear Y s i k) Ξ V ε) (he:0≤ε)
    (H:∀ u:ℝ, |u|≤1→Quotes (weighted flatP u (flatShear Y s i k)) w) (W:1≤ w)
    (hb:0≤B) (hb':B ≤1/2)(y:Phys (side Y i s)) :
    let T:= inclined Y s i k (atFrame Y s i x)
    ‖acts (T.glow (fullRead Y s i F (x.1,(Y.voyage i).CapeT s x))) y‖ ≤
      Real.exp (c+n_*WakeInvestment.fee K m V w ε B) * ‖acts (wholeTilt flatP 1) y‖ := by
  obtain ⟨σ,h,G,δ,g,z,p⟩:=A.pose
  let X:=(x.1,(Y.voyage i).CapeT s x); intro T; let f j:= flatSeat Y s i F j x; let S:= flatShear Y s i k
  have heq:(T.glow ∘ fun j=> F j X)=S.glow∘ f:=funext fun i'=>S.fold_use _ _
  rw [release,heq]; refine (leaf_pose flatP (flat_post Y s i k) S Ξ f G σ h K w ε V B m δ nK r he H W g (fun i u hu q=> (z i u q ((le_abs_self _).trans hu)).1) (fun i u hu q=> (z i u q ((le_abs_self _).trans hu)).2) hb hb' (fun i' j=> (A.comm i' j).map (unitStem (tradew _ (atFrame Y s i x))).glowHom) y (flatSea Y s i k) (preparedFlat Y s i k)).trans ?_
  apply mul_le_mul_of_nonneg_right (Real.exp_monotone _) (norm_nonneg _); simp_rw [onTicket] at p; linarith only [p]

lemma Fitting.actual (x:Orbit (side Y i s))(A:Fitting Y s i k K B c m F x)
    (nK:0≤ K) (r: Pillow (flatShear Y s i k) Ξ V ε) (he:0≤ε)
    (H:∀ u:ℝ, |u|≤1→Quotes (weighted flatP u (flatShear Y s i k)) w) (W:1≤ w)
    (hb:0≤B) (hb':B ≤1/2)(R':TiltInvoice Y s i k E)
    (h:s≤Y.uv k) :
    let G:=RootBook Y i k s; let S:=(Y.voyage i).CapeT s; let U:= recX P.U G S x
    ‖letterRead (fullRead Y s i F (x.1,S x)) U‖ ≤
       Real.exp ((Cascade.angleFin G.J.M (side Y i s) P.K.j) + c+n_*WakeInvestment.fee K m V w ε B+(3*dleaf P.R.L (shx s)+ ℰ s)*sites (N s i))*shadeY Y s i k 0 (Worth.gateC (shx s)) x := by
  intro G S U; let N':= side Y i s; let X:=(x.1,S x); let c':= Cascade.angleFin G.J.M N' P.K.j
  let g:= atFrame Y s i x; let T:= inclined Y s i k g
  let η := 3*dleaf P.R.L (shx s)*sites N'; let β:= WakeInvestment.fee K m V w ε B; let θ:= meterC (shx s)*sites N'
  let p:= shadeY Y s i k 0 (Worth.gateC (shx s)) x
  let F':= fullRead Y s i F X; let f:= mateK N'; let y:=acts (quant T.sell) U; let f':= acts (quant (star T.buy)) f
  have hz:‖f'‖=Real.exp c':=by
    unfold f' T inclined windShaft; rw [bra_fold]; let U':= tradew (side Y i s) g; let v:=acts (quantU U').val f
    have he: Sea (tickA N') v:=by have hx:= windLace U' (tickA N') f (tickB N'); rwa [Cascade.tick_g] at hx
    exact (saturation (nontrivial_spin P) (flat_post Y s i k) v (flatSea Y s i k) he (preparedFlat Y s i k)).1
  have ht:= Fitting.held Y s i k x A nK r he H W hb hb' y
  have hE:‖acts (wholeTilt flatP 1) y‖≤ Real.exp (η+θ)*p := R'.norm G.F G.slip G.K x η 1 (posture_ready G x (zero_le_one.trans P.height) (existingMarket Y s i k h)) (by norm_num)
  change ‖inner ℂ f (acts F' U)‖≤_; rw [T.lawn]; refine le_trans (norm_inner_le_norm f' (acts (T.glow F') y)) ?_
  rw [hz]; apply (mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le)) (Real.exp_pos _).le).trans_eq
  simp_rw [←mul_assoc,←Real.exp_add]; congr 2; ring

/-- Keep the signed angular equality ruling those estimates till this point, then put in Ice.
The hypothesis on integrating the (real) charge is a pure tilt estimate, to be proved separately
against G aperture. Use e.g. constant publisher e=C for link-independent polynomial tests; can also
pay an additional cost at ANY flagged faces in $X$ (input to the function $e$) via unused
`freeR` of shelter. -/
theorem actor_axis (R:ShelterRent Y s i k)(H:TiltInvoice Y s i k E)
    (e:Orbit (side Y i s)→ℝ)(κ:ℝ)(f: Fin n_ → Mark (side Y i s))
    (Z:∀ᵐ x : Orbit (side Y i s) ∂city (side Y i s), Fitting Y s i k K B (e x) m f x)
    (hκ:(Y.voyage i).kick ≤ k) (hx: Envelope (fullRead Y s i f))
    (p: Integrable (fun x=> Real.exp (e x)*shadeY Y s i k 0 (ηP s) x) (city _))
    (hz:(∫ x: Orbit _, Real.exp (e x)*shadeY Y s i k 0 (ηP s) x∂city (side Y i s)) ≤ Real.exp (κ+Papal.gBaseR Y s i k+7*(ℰ s)*sites (N s i)))
    (nK:0 ≤ K) (r: Pillow (flatShear Y s i k) Ξ V ε) (he:0≤ε)
    (A:∀ u:ℝ, |u|≤1→Quotes (weighted flatP u (flatShear Y s i k)) w) (W:1≤ w)
    (hb:0≤B) (hb':B ≤1/2) :
    ‖Journey.compass Y i k s (fullRead Y s i f)‖ ≤
        Real.exp (κ+n_*WakeInvestment.fee K m V w ε B+12*ℰ s*sites (N s i)) := by
  let G:=Gξ s i k; let N':= side Y i s; let S:=(ℂk s i); let b:=Papal.gBaseR Y s i k; let F:=fullRead Y s i f; let ρ : Orbit N' → ℂ := fun x=> letterRead (F (x.1,S x)) (Graph.recX P.U G S x)
  let g:= shadeY Y s i k 0 (ηP s); let β:=Cascade.angleFin G.J.M N' D
  let d:= sites N'; let ξ:=meterC (hat L P.x s); let M:= (3*dleaf L (hat L P.x s)+ξ)*d; let v:=Scales.merit P.R.L (hat L P.x s); let w':=n_*WakeInvestment.fee K m V w ε B+M
  let u:= ‖vac0 P.U G S‖; have hf:Real.exp (b+β-v*d)≤ u:=R.vast; have hu:0<u:= (Real.exp_pos _).trans_le hf; have hd:0 ≤d:= zero_le_one.trans (sites_pos _)
  change ‖markedRead F S (denZ G P.U S) / _‖ ≤ _; rw [←same_ratio,norm_div]; apply (div_le_iff₀ hu).mpr
  change ‖∫ x,ρ x∂city _‖ ≤ _; apply (norm_integral_le_integral_norm _).trans; have hp: Integrable ρ (city N'):=mark_integrable (Papal.roofage Y i s).bill hx ((Marks.can_read _ _ _ _ (Y.each_level i k s hκ R.paid)).smul (Complex.exp (-G.v)))
  refine le_trans (integral_mono_ae hp.norm (p.const_mul (Real.exp (β+w'))) ?_) ?_
  · filter_upwards [Z] with x hx
    apply le_trans (hx.actual Y s i k x nK r he A W hb hb' H R.paid); apply le_of_eq; rw [←mul_assoc (Real.exp _) (Real.exp _) (shadeY _ _ _ _ _ _ _),←Real.exp_add]; congr 2; unfold w'; abel
  rw [integral_const_mul]; apply le_trans (mul_le_mul_of_nonneg_left hz (Real.exp_pos _ |>.le)); refine le_trans ?_ (mul_le_mul_of_nonneg_left hf (Real.exp_pos _ |>.le)); rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
  have e0: ξ*d+7*ξ*d ≤ 8*ξ*d:= le_of_eq (by ring)
  have he: v*d≤ ξ*d:=mul_le_mul_of_nonneg_right R.health.1 hd; have ht: M ≤ 4*ξ*d:=by
    have g:dleaf L (hat L P.x s)≤ξ:=R.health.2.1; unfold M; linarith only [mul_le_mul_of_nonneg_right g hd]
  change β+w' + (κ+b+7*ξ*d)≤ κ+ n_*_+12*ξ*d+ _; unfold w'; linarith only [he,ht]

#print axioms actor_axis
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
