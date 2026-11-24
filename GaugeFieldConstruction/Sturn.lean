import GaugeFieldConstruction.Ciphering
import GaugeFieldConstruction.TurnTank
import GaugeFieldConstruction.Spree
set_option autoImplicit false
set_option maxHeartbeats 45000
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
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
open Fock.Flux Girt
local notation "Xq" s:max => hat P.R.L P.x s
variable {J:Type*} [DecidableEq J]
open Guide Fock.Flux
-- A generic BRACING. Coefficient lists charged by ℓ¹ budget. Use arbitrary lengths of white words, arbitrary Taylor coefficients before earth, check payoff for A. Package throat 'SunCap' independent of cred.
open Hood ProbabilityTheory Next.SectorChange.Gaussian
namespace FrameP
local notation "Hk" n:max => (FC (Single n))
variable (s i k:ℕ)
local notation "N'" => count Y s i
variable (V: Ropes (count Y s i))
abbrev θCA (q:Clip)(z:Signed)(δA:Site (More N'))(F:ℝ→ℝ)(x:Altar SU.group (More N')):= Aro Y s i k V (fun d=> F (d.θSlotA q z δA x))
lemma θDA (q:Clip)(z:Signed)(δA:Site (More N'))(F:ℝ→ℝ)(p:ContDiff ℝ 1 F):ContDiff ℝ 1 (θCA Y s i k V q z δA F):=by
 induction V with
 | nil=> unfold θCA; simp_rw [Aro_Ø]; exact contDiff_const
 | cons v w ih=>
     have he(l:List (Tick _ _)): ContDiff ℝ 1 (fun x: Altar SU.group (More (count Y s i))=>factorV l (fun j=>F (j.θSlotA q z δA x))):=by
        induction l with
        | nil=> exact contDiff_const
        | cons i l H=> exact ((p.comp (i.leadSA q z δA).contDiff).mul H)
     unfold θCA; simp_rw [Aro_step]; exact ((Complex.ofRealCLM.contDiff.comp (he v.2)).mul contDiff_const).add ih
variable {p:BudgetPoint}{q:Clip}{c:Clip}{F:PathData SU.group}{H:Bed}{η C S v δ κ w ξ R c':ℝ}
variable (B:F.Bounds q η C S) (P':Attached H F)
variable {d m u:ℕ}
lemma budget_θA (Φ: Signed)(δA:Site (More N'))(a:ℝ)(h:1≤a)(K:earshot Y s i k v)(e:1≤ v){S'}(r:∀ i∈V,Rubric S' d m i):let F(x:Altar SU.group (More N')):= θCA Y s i k V q Φ δA (parcel a) x
 (∀ x,‖F x‖ ≤ reliefR V * v^m*(2*a)^m) ∧ ∀ x y, ‖F x-F y‖≤ reliefR V*v^m*lipΔ q a m* bayColour (signX S' Φ δA) (x-y):=by
 have hp:= fun i v=> Ωcu Y s _ k K (r i v) -- i s shadow tune
 intro F
 induction V with
 | nil=> refine ⟨fun x=> ?_,fun x y=>?_⟩ <;> unfold F θCA <;> rw [relief_empty] <;> simp [Aro_Ø]
 | cons w l ih=>
    let T:=θCA Y s i k l q Φ δA (parcel a); let Z:=Ωsc Y s i k w; have he:= r w List.mem_cons_self
    let Y'(x:Altar SU.group (More N')):= factor_RA w.2 x q Φ δA (parcel a); have hx(x):F x=↑(Y' x)*Z+T x:= Aro_step ..
    obtain ⟨f,g⟩:= ih (r:=fun i v=>r i (List.mem_cons_of_mem _ v)) (hp:=fun i v=>hp i (List.mem_cons_of_mem _ v))
    rw [relief_cons]; refine ⟨fun x=> ?_,fun x y=>?_⟩ <;> simp_rw [hx]
    · apply (norm_add_le ..).trans; apply (add_le_add (show ‖(↑(Y' x):ℂ)*Z‖≤ ((2*a)^m)*(‖w.1.1‖*v^m) from ?_) (f x)).trans_eq
      · ring
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul ((θ_ballA Φ δA _ a h he.2.1).2 x) (hp w List.mem_cons_self) (norm_nonneg _) (by positivity)
    rw [show _- (↑(Y' y)*Z+T y)= (↑(Y' x-Y' y):ℂ)*Z+(T x-T y) by push_cast; ring]; apply (norm_add_le ..).trans; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]; exact (add_le_add (mul_le_mul (factor_θA Φ δA _ x y he.2.1 he.2.2 a h) (hp w List.mem_cons_self) (norm_nonneg _) (by have hk:= shade_b (signX S' Φ δA) (x-y); have h1:= q.quadratic_pos; unfold lipΔ longR; positivity)) (g x y)).trans_eq (by ring)
lemma buds_θA (Φ:Signed)(δA:Site (More N'))(a:ℝ)(h:1≤a)(K:earshot Y s i k v)(e:1≤ v){S'}(r:∀ i∈V,Rubric S' d m i):let H:=longR q
    ‖collectionS B P' (θCA Y s i k V q Φ δA id)‖ ≤ reliefR V* v^m*domeP H 1 m∧ ‖collectionS B P' (θCA Y s i k V q Φ δA (parcel a)) - collectionS B P' (θCA Y s i k V q Φ δA id)‖ ≤ reliefR V*v^m*(2*domeP H 2 m*Real.exp (-a)):=by
 intro H; let L:= v^m; let M:=domeP H 1 m; let P₀:=2*domeP H 2 m* Real.exp (-a);
 let n:=More N'; let X:=(stamen B P' n).starProjection; let μ:=stdGaussian (Altar G5 n)
 let E (W: Ropes (count Y s i))(p:ℝ→ℝ)(x:Altar G5 n):ℂ:= θCA Y s i k W q Φ δA p (X x); let Z:=parcel a
 have hz:0<a:=zero_lt_one.trans_le h
 have hh(W:Ropes N')(p:W⊆ V):
      Integrable (E W Z) μ ∧ Integrable (E W id) μ ∧ ‖∫ x, E W id x∂μ‖≤ reliefR W * L * M ∧ ‖(∫ x,E W Z x∂μ)-(∫ x,E W id x∂μ)‖ ≤ reliefR W * L* P₀:=by
   induction W with
   | nil=>
       have he(Y): E [] Y=0:= funext (fun x=> Aro_Ø ..); simp [he,relief_empty]; -- tune
   | cons w l ih=>
       obtain ⟨hp,hv,hr,hs⟩:= ih (fun i h=>p (List.mem_cons_of_mem _ h))
       have he:= r _ (p List.mem_cons_self); have ht:= Ωcu Y s i k K he; let D:=Ωsc Y s i k w; let V'(g:ℝ→ℝ)(x:Altar G5 n):= factor_RA w.2 (X x) q Φ δA g
       have hh(g x): E (w::l) g x=(↑(V' g x):ℂ)*D+ E l g x:= Aro_step ..
       obtain ⟨b,c,f,F,j⟩:= cuts_θA B P' Φ δA w.2 Z (parcel_diff a|>.continuous) a (fun _=> parcel_id hz) (fun i=>(parcel_cost hz i).2) he.2.1
       have hP(g:ℝ→ℝ)(t: Integrable (V' g) μ)(w': Integrable (E l g) μ): Integrable (E (w::l) g) μ∧ (∫ x,E (w::l) g x∂μ)= (↑(∫ x,V' g x∂μ):ℂ)*D+ (∫ x,E l g x∂μ):=by
          have hc: Integrable (fun x:Altar G5 n => (↑(V' g x):ℂ)) μ:= Complex.ofRealCLM.integrable_comp t; constructor; · rw [funext (hh g)]; exact (hc.mul_const D).add w'
          simp_rw [hh]; rw [integral_add (hc.mul_const D) w',integral_mul_const,integral_complex_ofReal] -- tune
       obtain ⟨p1,p2⟩:= hP Z b hp; obtain ⟨p3,p4⟩:=hP id c hv
       let cD(g):=∫ x,V' g x∂μ; let Q(g):= ∫ x,E l g x∂μ; rw [p2,p4,relief_cons]; refine ⟨p1,p3,?_,?_⟩
       · apply (norm_add_le ..).trans; rw [norm_mul,Complex.norm_real]; exact (add_le_add (mul_le_mul F ht (norm_nonneg _) (dome_W ..|>.le)) hr).trans_eq (by unfold M L; ring)
       rw [show _+_-( _*D+_)= ((↑(cD Z-cD id):ℂ)*D)+(Q Z-Q id) by change ↑(cD Z)*D+ Q Z-(↑(cD id)*D+ Q id)=_; push_cast; ring]; apply (norm_add_le ..).trans; rw [norm_mul,Complex.norm_real]
       have he: 0 < P₀:=by have hp:=dome_W H 2 m; unfold P₀; positivity; -- tune
       exact (add_le_add (mul_le_mul (show ‖cD Z-cD id‖≤ P₀ from j) ht (norm_nonneg _) he.le) hs).trans_eq (by unfold L; ring)
 exact (hh V (fun _ b=> b)).2.2
end FrameP
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
