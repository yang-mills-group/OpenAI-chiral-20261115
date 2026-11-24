import Palm.Mature
import Palm.Fabric
import Thin.Rail
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x : ℝ}
  {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi) (h : ℝ) (D C R0 : ℝ→ℝ) {N0 : ℕ} (T : Month x 1 6 2 N0 V W) (ht : T.q ≤ m.val)
  (S : Cape m B R.L) (ρ : ℕ→ℝ) (f : ℕ→ℝ) (k i : ℕ)
namespace Parcel
open Branch
open Pitching Pitching.Focus
variable {J q h D C R0 T S ρ f i}
variable (s:Parcel J q h D C R0 T ht S ρ f k)
variable {delay:ℝ}{P:Prescription R B}(H:Service V U W J q h D C R0 P N0 delay)(t:s.Prepared P delay)
variable (G:Morn K)(Q:Diary)(sk:G.After R)(Lq:ShelfTh G Q R0 D C J q h P N0 delay)
local notation "Yc"=> (hat R.L x i)
local notation "Ar"=> G.armor
local notation "w0"=> ((Actual T ht S f k).toSpine.address i)
local notation "fϕ"=> thinAllot G.Mult R Yc
local notation "fZ"=> (3*dleaf R.L Yc)

open Tune Roots Oath Bake Neon
attribute [-instance] instDecidableEqLex
variable {I:Type}[Fintype I][LinearOrder I]{Aρ qv ε:ℝ}(CA:Καlendar R G.armor qv Aρ G.Mult ε)
local notation "Nc" j:max=> cell m B R.L j
variable (xs:Site (cell m B R.L i)) -- unused
-- ABI
local notation "Mk"=> Mew.Key (LabelΩ I)
local notation "YΩ"=> hat R.L x i
local notation "ηκ" j:max=> (allotΨ R.L (hat R.L x j))
local notation "fi" i:max=> (mesh m R.L i)
local notation "St_" i:max=> (V.L.op (k-1-i) (kint m B R.L i))
variable (Ω:I→Site (cell m B R.L i))(v:Very_Ψ (N:=mesh m R.L i) (B:=B) Ω (s.gram i).p.B)
open scoped Mew
local notation "wrk" j:max=> ((Actual T ht S f k).toSpine.address j).step V
variable (d0 top:ℕ)(Ωs:∀ j:ℕ,I→Site (cell m B R.L j))
variable (Eξ:Mew.Key (LabelΩ I) → RegBudget (cell m B R.L top))(Kϕ:Mew.Key (LabelΩ I) → ForceBudget (cell m B R.L top))
/-- Like Hara.PalmL; exact solution with any start height here. Psi calibration.
$/ -/
structure ClockRec (E:∀ j:ℕ,Mew.Key (LabelΩ I) → RegBudget (cell m B R.L j))(Kz:∀ j:ℕ,Mew.Key (LabelΩ I) → ForceBudget (cell m B R.L j))(C:ℕ→ (LabelΩ I)→ LabelΩ I →ℂ):Prop where
 born: E top=Eξ ∧ Kz top=Kϕ
 root (j:ℕ): d0 ≤ j → j≤top → Leaf_R (N:=mesh m R.L j) (B:=B) (s.gram j) (Ωs j) (E j) (Kz j) h G.Mult Aρ (allotΨ R.L (hat R.L x j)) R.L
 spin (j:ℕ): d0≤ j → j<top →Bijective (Roots.toV_C (Cube.node ∘ xΞ (Ωs j)) (C j)) ∧ (∀ z∈Mew.hill (LabelΩ I),∀ i:LabelΩ I, ‖Roots.toV_C (Cube.node ∘ xΞ (Ωs j)) (C j) z i‖≤ pass_C R.L qv) ∧ χHome (X:=s.gram j) (Y:=s.gram (j+1)) (G₀:=S j) (G₁:=S (j+1)) (q:=q) (U:=U) (kL:=J.d)
          V (Ωs j) (E (j+1)) (Kz (j+1)) (apt m B R.L j) (((Actual T ht S f k).toSpine.address j).step V) (s.wave j).val (E j) (Kz j) (C j)
include H t sk Lq CA
theorem threadClock (headJ:Leaf_R (N:=mesh m R.L top) (B:=B) (s.gram top) (Ωs top) Eξ Kϕ h G.Mult Aρ (ηκ top) R.L)(leg:top≤k)(hl: d0≤top)
    (pD:Very_Ψ (N:=mesh m R.L d0) (B:=B) (Ωs d0) (s.gram d0).p.B)(eO:∀ i,d0 ≤ i→ i<top→ Ωs (i+1)=Hove.heel (apt m B R.L i) ∘ Ωs i)
    (hr:∀ i ≥ d0,let y:=hat R.L x i; Ready_K R.L y ∧ Lens_K R G.cap (PongR R.L) (pass_C R.L qv) y (Q.Z y) (Q.W y) (Q.V1 y) (Q.KR y))(hu: 1≤h):
    ∃ E Kz C, ClockRec (qv:=qv) (Aρ:=Aρ) ht k s G d0 top Ωs Eξ Kϕ E Kz C:=by
 let Bx(j:ℕ):=(s.gram j).p.B
 have he (j:ℕ)(p:d0≤j)(v:j ≤ top): Very_Ψ (N:=mesh m R.L j) (B:=B) (Ωs j) (Bx j):=by
    induction j,p using Nat.le_induction with
    | base=>exact pD
    | succ j p ih=>
      have hv0:j< top:=v
      have he:= ih hv0.le
      have eq:=eO _ p hv0
      have hl: Bx (j+1) ≤2*Bx j:=by
        unfold Bx
        rw [gramBound ht k s t (j+1) (v.trans leg),gramBound ht k s t j (hv0.le.trans leg),heroΘ]
        exact (hr j p).1.cost _ le_rfl
      rw [eq]; exact balm_k R.L _ he hl rfl R.odd_side CA.side
 suffices Q:∀ j:ℕ, d0+j≤top→∃ E Kz C,ClockRec (qv:=qv) (Aρ:=Aρ) ht k s G (top-j) top Ωs Eξ Kϕ E Kz C by
    have hb:=Q (top-d0) (by omega); rwa [(by omega:top-(top-d0)=d0)] at hb
 intro r hk; induction r
 case zero=>
    let E(t:ℕ): Mew.Key (LabelΩ I)→ RegBudget (cell m B R.L t):=if z:t= top then z ▸ Eξ else 0; let F(t:ℕ): Mew.Key (LabelΩ I)→ ForceBudget (cell m B R.L t):= if v:t= top then v ▸ Kϕ else 0; have he:E top= Eξ:=by unfold E; rw [dif_pos rfl]
    have hf:F top=Kϕ:=by unfold F; rw [dif_pos rfl]
    refine ⟨E,F,0,⟨he,hf⟩,fun i v h=>?_ ,fun j v h'=>by omega⟩
    have hz:i=top:=by omega
    subst i; rw [he,hf]; exact headJ
 case succ a ih=>
    have h0:d0+a≤top:=by omega
    obtain ⟨E0,K0,V1,pX⟩:=ih h0; let i:= top-(a+1); have h:d0≤ i:=by unfold i; omega
    have u:i<top:=by unfold i; omega
    have hm:top-a=i+1:=by unfold i; omega
    let hc:=pX.root (i+1) hm.le u
    have e:=eO _ h u
    obtain ⟨F'μ,Gμ,Qμ,ha,Uq,U',χ⟩:= stages ht k s H t G Q sk Lq CA (Ωs i) (he i h u.le) (E0 (i+1)) (K0 (i+1)) (e ▸ hc) (u.trans_le leg) (hr i h) hu
    let E':= Function.update E0 i F'μ; let W':= Function.update K0 i Gμ; let G_:= Function.update V1 i Qμ
    have he:E' i=F'μ:=Function.update_self ..; have hv:W' i=Gμ:=Function.update_self ..; have hs:G_ i=Qμ:=Function.update_self ..
    refine ⟨E',W',G_,⟨(Function.update_of_ne u.ne' ..).trans pX.born.1,(Function.update_of_ne u.ne' ..).trans pX.born.2⟩,fun j (p : i≤ j) v=>?_ ,fun j (p : i ≤ j) z=>?_ ⟩
    · rcases p.eq_or_lt with a|a
      · subst j; rw [he,hv]; exact U'
      unfold E' W'; rw [Function.update_of_ne a.ne', Function.update_of_ne a.ne']; exact pX.root j (hm ▸ a) v
    rcases p.eq_or_lt with h|h; swap
    · unfold E' W' G_; simp_rw [Function.update_of_ne (show j+1≠i from by omega),Function.update_of_ne h.ne']; exact pX.spin j (hm ▸ h) z
    subst j; rw [show E' (i+1)=E0 _ from Function.update_of_ne (by omega:i+1≠i) ..,show W' (i+1)=K0 _ from Function.update_of_ne (by omega:i+1≠i) ..,he,hv,hs]; exact ⟨ha,Uq,χ⟩
#check ClockRec
end Parcel
end YM.CF.Py.Rate
