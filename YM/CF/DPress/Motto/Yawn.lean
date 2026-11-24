import YM.CF.DPress.Motto.Ear
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open DPress.Plaque Larch Ione Taxi
namespace WagesC
variable {n:Side}{k L:ℕ}(P:BudgetPoint){a h:ℝ}(w:Wings k P a n)(z:ℝ)
-- equivariant if not wrapped sparse. Target beta α/E meeting.L
open StressFlux
local notation "M" => Point n
local notation "A"=> (αLan (n:=n) z)
lemma wage0 (X:Scree.Hub n)(p:Pane n): wage_Q 0 (A X p)=A X p:=by
 suffices blind_E (A X p) =0 from (sub_eq_zero.mp this).symm
 change cut_V ((αLan z X) p)=0; unfold αLan; split; next h=> rw [pureQ,Pi.smul_apply,map_smul,fund,mon_v,show cut_V (hollow _)=0 from oqua (n:=n) _ ,smul_zero] -- existence csmul
 next h=> exact map_zero _
lemma tip : cry_H A=A:= by apply funext; intro i; exact funext fun j=>wage0 z i j
variable (u:1<L)
include w u
lemma enjoy(v:M): chute P L (hup v) := lt_of_le_of_lt (pow_le_pow_left' (covers P w v) 3) (by change 1^3<L; simpa)
lemma δat(v:M): Taxi.realH (caw P L (cry_H A)) (hup v)= z • feeW v:=by
 rw [tip]; unfold Taxi.realH caw; rw [if_pos (enjoy P w u v)]; funext i; unfold αLan; rw [if_pos rfl]; change Complex.re (Beau.pot ∅ (z • (moldV n (feeW v i))))= _; rw [map_smul,Beau.mold_l,Complex.smul_re]; rfl -- tune
lemma spanL(v:M): Nonwrapping (Taxi.villa (hup v)) v :=by
 have ht:haloW v ⊆ halo 6 {v}:=Corona.halo_mono (by decide : (2:ℕ)≤6) (Subset.refl _); let a:=6; intro i f; have hv:i∈halo 6 {v}:= union_subset ht (Subset.refl _) f; obtain ⟨g,p,r⟩:=halo_spec.mp hv; rw [mem_singleton.mp p,separation_comm] at r; have he:= w.hn; unfold qualify at he; omega
-- w.v Persona SPD symmetry risk.Prime
lemma fluxι (v:M)(r:PlaqAxes): fluxP (hup v) (Taxi.realH (caw P L (cry_H A)) (hup v)) r r=z:=by
 rw [δat P w z u]; unfold fluxP; rw [if_pos (show Nonwrapping _ _ from spanL P w u v)]; let V:= AnalyticBridge.VerifiedReset.wedge r (spike SU.group); let P0:= V.field v; change logHessian _ P0 P0=z
 have ht:= Plaque.hessian P v V w.hn (by rw [separation_self]; omega : separation v v≤k); have he: logHessian (feeW v) P0 P0=1:=by
    refine ht.trans ?_; unfold V; rw [sum_eq_single r]; swap; · intro i _ q; rw [curl_wedge,if_neg (Ne.symm q),norm_zero,zero_pow (by decide:2≠0)]
    swap; · simp
    rw [curl_wedge,if_pos rfl,spike_norm Thera.yet_one,one_pow] -- tune
 let T:= (![P0,P0]:Fin 2→tangD n); change iteratedFDeriv ℝ 2 (z • (feeW v ∘ RG.increment 1)) 0 T = z; rw [iteratedFDeriv_const_smul_apply (i:=2) ((Plaque.diff v 1).contDiffAt.of_le le_top),_root_.smul_apply]; change z*logHessian (feeW v) P0 P0=z; rw [he,mul_one]
omit w u
lemma awayF(X:Scree.Hub n)(g:X≠hup X.val.1): fluxP X (Taxi.realH (caw P L (cry_H A)) X)=0:=by
 have he: Taxi.realH (caw P L (cry_H A)) X= fun _=>0:=by rw [tip]; unfold Taxi.realH caw; rw [show αLan z X=0 from if_neg g,ite_self]; rfl
 funext i j; rw [he]; unfold fluxP; split; swap; rfl
 exact AnalyticBridge.VerifiedReset.hessian_zero (0:ℝ) _ _
lemma put_b(q:Site n): ∑ i:Site n,Taxi.motto i q=1:=by
 unfold Taxi.motto; rw [←mul_sum,sum_comm]; have he(j:Taxi.Marca):(∑ x:Site n, if q=x+Taxi.boot j then (1:ℝ) else 0)=1:= by
    simp_rw [show ∀ x:Site n,q=x+Taxi.boot j ↔ x=q-Taxi.boot j from (fun x=>eq_comm.trans eq_sub_iff_add_eq.symm)]; simp
 simp_rw [he,sum_const,card_univ,nsmul_eq_mul,mul_one]; exact inv_mul_cancel₀ (by positivity : (Fintype.card Taxi.Marca:ℝ)≠0) -- tune
include w u
lemma δPawn : aora P L A = z:=by
 unfold aora lureC payoutF; let r:= Averaging.axes01; let T:= Taxi.realH (caw P L (cry_H A)); let F(i:Scree.Hub n):=motto i.val.1 (0:M)*fluxP i (T i) r r; change ∑ i,F i=z; rw [←sum_fiberwise (g:=fun i:Scree.Hub n=> i.val.1)]; -- sum_fiberwise binder
 have h(v:Point n):(∑ i:Scree.Hub n with i.val.1=v,F i)= motto v 0*z:=by
    rw [sum_eq_single (hup v)]; · unfold F T; rw [fluxι P w z u]; -- tune rfl
    · intro i v' h; unfold F T; rw [awayF P z (L:=L) i (by rw [(mem_filter.mp v').2]; exact h)]; simp
    exact fun g=> (g (mem_filter.mpr ⟨mem_univ _,rfl⟩)).elim
 simp_rw [h,← sum_mul,put_b,one_mul] -- tune
end WagesC
end YM.CF.Py.Kay
