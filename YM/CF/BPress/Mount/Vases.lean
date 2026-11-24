import YM.CF.BPress.Mount.Silhouette
/- pipeline Mark assembly. $add at every band. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mount
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree Voice Noon Phase Extensor Stamps Grid Hazel Net Locale Push.AbsoluteSums --
variable {s m B N:Side} {D:BandWidth}{T:Sheet.Atlas}{X Y Z W:Pledge}{a:ℕ}{c d L y u v μ q ε:ℝ}{R:Driver (mid m B)}{P: Edition R}{G:Brace.Duet m B}{U:GramM (mid m B)}{p:Wish R X Y Z}
namespace Awards
variable {K:Type}{g:K→R.Pose}
section generic
variable (A:Bands (More N) D)(F:Net (More N) T L y c d a)(H:Paint (More N)) (h:Tiling (More N)) (s z:List A.Index)(V: Phys N)(x:Orbit N)(u:A.Slates)
def LeftArea : Support N := s.toFinset.biUnion (fun i=> Chalk.withinX (A.band i))
abbrev clueT (i:A.Index): toolsF N:= (x.1, A.putF T y x.1 i (u i)) -- F dummy likely wants F
abbrev autograph (u:A.Slates)(p:Orbit N)(H:Paint (More N)):Prop:= ∀ (i:A.Index)(k:Site N),node k∈A.band i→ spline A F h i (clueT (T:=T) (y:=y) A p u i) 2 (node k)= H (node k)
lemma univ_pays (t:∀ i,i∈s): (univ : Support N)\ LeftArea A s=Lily.vacancy A:=by
 have he:s.toFinset=univ:= eq_univ_iff_forall ..|>.2 (fun i=> List.mem_toFinset.mpr (t i)); rw [LeftArea,he]; ext i; simp [Lily.vacancy,Hazel.Welkin, Chalk.withinX] -- tune
lemma point_β (p:s.Nodup)(t: autograph A F h u x H)(k:MatPlan H)(S:Support N)(u':LeftArea A s⊆S) : inner ℂ (holdα S H) (acts (readout (T:=T) (y:=y) A s (fun i=>Chalk.pairTest A i F h) u x.1) V)= inner ℂ (holdα (S\LeftArea A s) H) V:=by -- T implicit confusion
 induction s generalizing S with| nil=> simp [LeftArea, Net.readout, walkMul]|cons i l ih=>
    let M:=Chalk.withinX (A.band i); let R:=LeftArea A l; have hp: LeftArea A (i::l)=M∪ R:=by rw [LeftArea,List.toFinset_cons,biUnion_insert]; rfl
    have he: M⊆S:=fun x p=> u' (hp.symm ▸ mem_union_left _ p); let Z':= clueT (T:=T) (y:=y) A x u i; let V': FC _:= readout (T:=T) (y:=y) A l (fun i=> Chalk.pairTest A i F h) u x.1
    rw [show readout _ _ _ _ _= _ from (show readout (T:=T) (y:=y) A (i::l) (fun i=> Chalk.pairTest A i F h) u x.1= Chalk.pairTest A i F h Z'* V' from rfl),hp, show S \ (M∪R)= (S\M) \ R from (sdiff_sdiff S M R).symm]; rw [act_mul]; refine Eq.trans (Chalk.pairRead A i F h x.1 Z'.2 S H _ he (t i) k) (ih (List.nodup_cons.mp p).2 _ ?_); intro b v; obtain ⟨j,s,r⟩:= mem_biUnion.mp v; apply Finset.mem_sdiff.mpr; refine ⟨u' (hp.symm ▸ mem_union_right _ v),fun g=>?_ ⟩; exact disjoint_left.mp (A.band_disjoint (show i≠j from fun q=> (List.nodup_cons.mp p).1 (q.symm ▸ List.mem_toFinset.mp s))) (mem_filter.mp g|>.2) (mem_filter.mp r|>.2)
lemma pays_total (k:s.Nodup)(l:∀ i,i∈s)(t: autograph A F h u x H)(p:MatPlan H): beamZ N (acts (readout (T:=T) (y:=y) A s (fun i=> Chalk.pairTest A i F h) u x.1) V)= inner ℂ (holdα (Lily.vacancy A) H) V:=by rw [beamZ,← univ_pays A s l,← Chalk.woven_mate H p];  rw [← Chalk.woven_unit]; exact point_β A F H h s V x u k t p univ (subset_univ _)
end generic
end Awards
end YM.CF.BPress.Mount
