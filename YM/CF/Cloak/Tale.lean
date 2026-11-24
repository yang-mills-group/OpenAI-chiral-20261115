import YM.CF.Cloak.Grasp
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
section bound
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x₀:E}{U:E→ Config G f}{u v C D:ℝ}{T:E→X}[NormedAddCommGroup X][NormedSpace ℝ X]
local notation "m"=> SU.group.colorScale
open scoped Classical
variable {X₂:Support f}{U₀:Config G f}{A:Finset (Cell f)}{F:Forest S.ratio}{s:ℝ}
open Atala
lemma joint_s (n:ℕ)(r:ℕ):∃ p C:ℝ, 0<p∧m ≤ C∧1 ≤ C∧∀ {f:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G f)(x:E)(t:ℝ), 0≤t→ t≤p→ Trow U x t n →∀ (s:Signed)(i:Site f)(w:Walk), w.length≤r→ Tender (fun y=>travel (pull s 0 (U y)) i w) x (C*t) n:=by
 let a:=firstRadius G; have ha:0<a:=first_pos G; obtain ⟨p,C,h,hC,H,V,I⟩:=sailors n Chi.canonical (div_pos ha (by norm_num : (3:ℝ)>0)) (show 2*(a/3)< _ by unfold a at *; linarith)
 let z:=C^(r+2); have he:0<C:=zero_lt_one.trans_le hC; have hz:0<z:=pow_pos he _; let e:=p/z; refine ⟨e,max m z,div_pos h hz,le_max_left ..,(one_le_pow₀ hC).trans (le_max_right ..),@fun f E _ _ U x t g hg hf s i w hw=>?_⟩
 have h0: z*t ≤ p:=(mul_comm z t).le.trans ((le_div_iff₀ hz).mp hg)
 let K(n):=Cash n t C; have hh(n:ℕ)(k:n≤r+2): K n ≤ p:=(take_k hC g k).trans h0
 have hy(j:Bond f) : Tender (fun y=>pull s 0 (U y) j) x (K 1) n:=by
    simp_rw [ProjectorNext.Equivariance.pull_formula]; split
    next =>
       have ht:t ≤ p:=by simpa [K,Cash] using hh 0 (by omega)
       exact (show C*t=K 1 by simp [K,Cash]) ▸ V.duty ht (hf _) (hf j)
    next => exact (hf _).bag (by unfold K Cash; rw [pow_one]; exact le_mul_of_one_le_left g hC)
 have he(i:Site f)(w:Walk)(h:w.length≤r): Tender (fun y=>travel (pull s 0 (U y)) i w) x (K (w.length+2)) n:=by
    induction w generalizing i with
    | nil => exact (Shake.holds (SU.group.mat 1)).bag (mul_nonneg (pow_nonneg he.le _) g)
    | cons d w ih=>
       have hx:w.length ≤r:=Nat.le_trans (by simp) h; let X(y):= Step.read d (pull s 0 (U y)) i; let Y:= ih (i+d.vec) hx; have ht:K 2 ≤ K (w.length+2):= take_k hC g (by omega)
       have he:Tender X x (K 2) n:=by
          unfold X Step.read; split
          next => exact (show C*K 1=K 2 from put_c 1 t C) ▸ V.duty (hh 1 (by omega)) (hy _) (hy (i,0)) -- need equal $$2 conversion
          next => exact (hy _).bag (take_k hC g (by decide: 1≤2))
       rw [List.length_cons,show w.length+1+2=w.length+2+1 from rfl]; exact (show C*K (w.length+2)=K (w.length+2+1) from put_c ..) ▸ H.duty (hh _ (by omega:w.length+2 ≤ r+2)) (he.bag ht) Y -- tune
 exact (he i w hw).bag ((take_k hC g (by omega:w.length+2 ≤ r+2)).trans (mul_le_mul_of_nonneg_right (le_max_right ..) g))
lemma loc_k (Y:Support f)(p:Healthy t Y U₀)(i: Cell f)(h:i∈costA Y) : Pressure.toll U₀ i ≤ t:= (green_k _ _ _).mp p _ (mem_inter.mpr ⟨mem_univ _,h⟩)
lemma tintB (q:RG.Atom G n)(x:Site f)(i:Fin n): Work.F03.slotFace (q.leg i) x ∈ costA (q.footprint x):=by
 let s:=q.leg i; let P:= Work.F03.slotFace s x; refine mem_filter.mpr ⟨mem_univ _,fun h=>Finset.disjoint_left.mp h (show P.1∈ q.footprint x from ?_) (Work.E01.base_touched _) ⟩ -- tune
 refine mem_image.mpr ⟨s.offset,mem_insert_of_mem ?_,rfl⟩; refine mem_biUnion.mpr ⟨i,mem_univ _,mem_union_right _ ?_⟩; exact List.mem_toFinset.mpr (show s.offset∈ s.offset::_ from List.mem_cons_self)
end bound
end YM.CF.Cloak
