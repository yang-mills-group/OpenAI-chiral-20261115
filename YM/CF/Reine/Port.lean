import YM.CF.Reine.Reed
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Reine
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti Cay Slate Forge Bloch Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {s:Signed}
section
open scoped Classical
-- kernel comparison on coarse config in one frame channel
variable {o:Support c}(p:ZoneB T x o U V)(hp:0<fiery G x S.patch.L)
local notation "B₀"=>radiusB x
local notation "r₀"=>Stores.till x
local notation "t₀"=>fiery G x S.patch.L
local notation "E₀"=>temp x

include p
lemma reached_g{α:Type}[Fintype α](K:α→ Twin c → Pressure.Pay G)(i: α)(y:α→Site c)(hK:∀ i j,separation (y i) j.1.1 > r₀ → K i j=0)(h:y i∉halo (B₀+r₀) o): zip K (wV T r₀ E₀ ∅ V) i=zip K (T.vision r₀ E₀ V) i:=by
   simp only [zip]
   refine sum_congr rfl fun j _=> ?_
   by_cases u:separation (y i) j.1.1 > Stores.till x
   next =>
     rw [hK i j u]; simp
   rw [k_vis (i:=j) p (afar_s _ _ _ h (by rw [separation_comm j.1.1]; omega))]
lemma cing{α:Type}[Fintype α](K:α→ Twin c → Pressure.Pay G)(j:Twin c)(y:α→Site c)(hK:∀ i j,separation (y i) j.1.1 > r₀ → K i j=0)(h:j.1.1∉halo (B₀+r₀+r₀) o): unzip K (zip K (wV T r₀ E₀ ∅ V)) j= unzip K (zip K (T.vision r₀ E₀ V)) j:=by
   simp only [unzip]
   refine sum_congr rfl fun i _=> ?_
   by_cases u:separation (y i) j.1.1 > Stores.till x
   next =>
     rw [hK i j u]; simp
   rw [reached_g p K i y hK (afar_s _ _ _ h (by omega))]

omit p
private lemma pf' (i:Twin f)(j:Twin c){V:Config G c}{T:Tube G S}(v:separation (S.ratio.parent i.1.1) j.1.1>Stores.till x): T.Φ (Stores.till x) V i j=0:=Offset.leap_bound V _ _ v.not_ge
abbrev taxM(x:ℝ):= radiusB x +Stores.till x+Stores.till x +10
def payX (T:Tube G S)(x:ℝ)(o:Dill S):= let R:= Stores.till x; let t:= temp x; fun (U:Config G f)(Q V:Config G c)=> Sum.elim (T.workF R U V (fiery G x S.patch.L) t) (Sum.elim (T.workI R Q V t) (Sum.elim (fun i=>T.workC R V t i+(T.workL R U Q V t i+ T.workD R V t i)) (T.workN R V t))) o
abbrev atM(S:StepData c f): Dill S → Site c:=Sum.elim (fun i=>S.ratio.parent i.1) (Sum.elim Prod.fst (Sum.elim Prod.fst Prod.fst))
include p hp
lemma bay(v:Dill S)(h:atM S v ∉halo (taxM x) o): Yaught T r₀ t₀ E₀ V U k v=payX T x v U (S.prediction U k) V:=by
   let f₁:= S.prediction U k
   let K:=wit V f₁
   have hk:kZ (S:=S) K=Tube.Z S f₁ V:=rfl
   unfold taxM at h
   rcases v with i|i|i|i
   next =>
     change S.ratio.parent i.1 ∉halo (B₀+r₀+r₀+10) o at h
     have he(j:Bool):zF T r₀ E₀ ∅ V (i,j)=T.Mv r₀ E₀ V (i,j):= reached_g p _ (i,j) (fun k:Twin f=> S.ratio.parent k.1.1) (fun i j=>pf' (T:=T) (V:=V) i j) (fun z=>h (Corona.halo_mono (by omega) (Finset.Subset.refl _) z))
     unfold Yaught payX
     simp only [Sum.elim_inl]
     unfold kF workF
     rw [bill_x p hp i (fun l=> h (Corona.halo_mono (by omega) (Finset.Subset.refl _) l))]
     simp_rw [he]
   next =>
     change i.1∉halo (B₀+r₀+r₀+10) o at h
     have he:zI T r₀ E₀ ∅ V i=T.Mw r₀ E₀ V i:=reached_g p _ i Prod.fst zI_span (fun z=>h (Corona.halo_mono (by omega) (Finset.Subset.refl _) z))
     unfold Yaught payX
     simp only [Sum.elim_inr,Sum.elim_inl]
     unfold kI workI
     congr 1
     unfold monetary wire wit
     rw [fare_h,SU.group.chord_price]
     ring
     rw [he]; rfl
   next =>
     change i.1∉halo (B₀+r₀+r₀+10) o at h
     have he(j:Bool): wV T r₀ E₀ ∅ V (i,j)=T.vision r₀ E₀ V (i,j):= k_vis p (fun z=> h (Corona.halo_mono (by omega) (Finset.Subset.refl _) z))
     let R:= wV T r₀ E₀ ∅ V
     let Q:=T.vision r₀ E₀ V
     have hv{α:Type}[Fintype α](K:α→Twin c→Pressure.Pay G)(Y:α→Site c)(g:∀ i j,separation (Y i) j.1.1 > r₀ → K i j=0)(j:Bool): unzip K (zip K R) (i,j) = unzip K (zip K Q) (i,j):= cing p K (i,j) Y g (fun z=> h (Corona.halo_mono (by omega) (Finset.Subset.refl _) z))
     unfold R Q at hv
     unfold Yaught payX
     simp only [Sum.elim_inr,Sum.elim_inl]
     unfold kC kL kD zI zF
     unfold workC workL workD Mv Mw
     change _= _
     unfold K f₁ at hk
     simp_rw [hk,he,hv (T.Φ (Stores.till x) V) (fun i:Twin f=> S.ratio.parent i.1.1) (fun i j=> pf' i j),hv (T.Φ' (Stores.till x) V) Prod.fst zI_span,hv (T.N (Stores.till x) V) Prod.fst reachN, kin_c p (i:=i) (fun z=> h (Corona.halo_mono (by omega) (Finset.Subset.refl _) z))]
   change i.1∉halo (B₀+r₀+r₀+10) o at h
   have he:= reached_g p (T.N r₀ V) i Prod.fst reachN (fun z=> h (Corona.halo_mono (by omega) (Finset.Subset.refl _) z))
   unfold Yaught payX
   simp only [Sum.elim_inr]
   unfold kN workN
   rw [he]
end
end YM.CF.Reine
