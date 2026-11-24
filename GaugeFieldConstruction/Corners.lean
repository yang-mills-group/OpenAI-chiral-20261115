import GaugeFieldConstruction.Sells

/-!
# Don't have to move probes off their domains to identify the rotations
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Calibration.RawBank
open Gap Cauchy Conj Row Phys Function Submodule U1 Flux One Stage Wide Stage.Cell One.Lamp Floor
open Matter (Slot FlavorIndex)
open scoped BigOperators Topology ContDiff

theorem exists_path (x y:E4) (h:x≠y) :∃ χ, Chassis x y χ := by
  obtain ⟨r,hr,h⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (isOpen_compl_singleton.mem_nhds (show x∈({y}:Set E4)ᶜ from h))
  let p : ContDiffBump x:=⟨r/2,r,by positivity,by linarith⟩
  refine ⟨p,⟨p.contDiff,p.hasCompactSupport⟩,p.eventuallyEq_one,?_⟩ -- nested
  rw [p.tsupport_eq]; exact fun v=>h v rfl -- tune
lemma shine (d) (x : UV d) (p : ∀ b:Book, eye Wick.apex (Wick.pair (dress (shells d x)) b)=0): x=0 := by
  let H:=spinFrame d Mirror.mirror
  have he : ∀ (u:UV d), H (H u)=u := fun u=>by
    change _=_; rw [← Module.End.mul_apply]; unfold H; rw [← map_mul,show Mirror.mirror*Mirror.mirror=1 by ext <;> simp [Mirror.mirror,Signed.mirror],map_one]; rfl -- defeq?
  let y:=shade d (H x)
  have hp: shade d (H y)=x := by rw [show y = shade d (H x) from rfl,show H (shade _ _)= shade d (H (H x)) from Eq.symm (comp_s Mirror.mirror (H x)), he, clear]
  by_contra q; have ht : y≠0:= fun h=>q (by rw [← hp,h,map_zero,map_zero])
  have hh := Invoice.mirror_positive d y ht
  change 0<(eye _ (Wick.pair (dress (shells d (shade d (H y)))) _)).re at hh
  rw [hp,p] at hh; simp at hh

lemma owned_t (k : FlavorIndex) (d) (a : UF d) : graph_f ((shells d (0,0,Pi.single k a,0)).2.2.1)=tiap k a.val := by
  unfold graph_f; rw [LinearMap.sum_apply]; rw [Finset.sum_eq_single k]
  · simp only [LinearMap.comp_apply,shells,LinearMap.prodMap_apply,LinearMap.proj_apply, mv_at,Pi.single_eq_same,Submodule.subtype_apply]
  · intro b _ h; simp only [LinearMap.comp_apply,shells,LinearMap.prodMap_apply,LinearMap.proj_apply,mv_at,Pi.single_eq_of_ne h,map_zero]
  simp
lemma other (k : FlavorIndex) (d) (a : UX d) : graph_x ((shells d (0,0,0,Pi.single k a)).2.2.2)=tuap k a.val := by
  unfold graph_x; rw [LinearMap.sum_apply]; rw [Finset.sum_eq_single k]
  · simp only [LinearMap.comp_apply,shells,LinearMap.prodMap_apply,LinearMap.proj_apply, mv_at,Pi.single_eq_same,Submodule.subtype_apply]
  · intro b _ h; simp only [LinearMap.comp_apply,shells,LinearMap.prodMap_apply,LinearMap.proj_apply,mv_at,Pi.single_eq_of_ne h,map_zero]
  simp
lemma cand (d : Floor) (c : UV d) (h : c.2.2.2=0): (dress (shells d c)).2.2.2=0 := by rw [dressX]; simp only [shells,LinearMap.prodMap_apply,h,map_zero]
lemma card (d : Floor) (c : UV d) (h:c.2.2.1=0): (dress (shells d c)).2.2.1=0:=by rw [dressF]; simp only [shells,LinearMap.prodMap_apply,h,map_zero]
lemma cold (d : Floor) (c : UV d) (h:c.2.1=0): (dress (shells d c)).2.1=0 := by rw [dressG]; simp only [shells,LinearMap.prodMap_apply,h,map_zero]

lemma globe {d} (T : Axis→Axis→J GaugePair) (c : UG d) (p : ∀ u,(gloG T).cost 0 Wick.apex (graph_g c.val) u=0) : c=0 := by
  let q : UV d := (0,c,0,0)
  have H : q=0 := shine d q fun b=>by
    change eye _ (Wick.cyc (dress _) _)=_; unfold Wick.cyc
    rw [show (dress (shells d q)).1=0 from rfl,zero_mul,zero_smul,zero_add, card d q rfl,cand d q rfl, map_zero, map_zero]; simp only [LinearMap.zero_apply, add_zero];
    have h:= p b.2.1; rw [shineG,sub_zero] at h; exact h
  exact congr_arg (fun a : UV d=>a.2.1) H
lemma gloss {d} (T :Axis→Axis→J Spair) (k : FlavorIndex) (c : UF d) (p : ∀ u,(gloF T).cost 0 Wick.apex (tiap k c.val) u=0) : c=0 := by
  let q : UV d:= (0,0,Pi.single k c,0)
  have H : q=0:= shine d q fun b=>by
    change eye _ (Wick.cyc (dress _) _)=_; unfold Wick.cyc
    rw [show (dress (shells d q)).1=0 from rfl,zero_mul,zero_smul,zero_add,cold d q rfl,cand d q rfl,dressF,owned_t,map_zero,map_zero]; simp only [LinearMap.zero_apply,zero_add,add_zero]
    have h:=p b.2.2.1; rw [shineF,sub_zero] at h; exact h
  have h:= congr_arg (fun a : UV d=> a.2.2.1 k) H; change (Pi.single k c:Fragment (UF d)) k=0 at h; simpa only [Pi.single_eq_same] using h
lemma glass {d} (S : Axis→Axis→J Spair) (T : Axis→Axis→J GaugePair) (k : FlavorIndex) (c : UX d) (p : ∀ u,(gloX S T).cost 0 Wick.apex (tuap k c.val) u=0): c=0 := by
  let q : UV d:=(0,0,0,Pi.single k c)
  have H : q=0:= shine d q fun b=>by
    change eye _ (Wick.cyc (dress _) _)=_; unfold Wick.cyc
    rw [show (dress (shells d q)).1=0 from rfl,zero_mul,zero_smul,zero_add,cold d q rfl,card d q rfl,dressX,other,map_zero,map_zero]; simp only [LinearMap.zero_apply,zero_add]
    have h:=p b.2.2.2; rw [shineX,sub_zero] at h; exact h
  have h:=congr_arg (fun a:UV d=>a.2.2.2 k) H; change (Pi.single k c:Fragment (UX d)) k=0 at h; rwa [Pi.single_eq_same] at h
end YM.GaugeFieldConstruction.Calibration.RawBank
