import YM.CF.Mir.Group

/-! Grid rotational pull on links and labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mir.Trip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} (b : Trip m)
lemma step_plane (x : Site (Domain m B)) (i : Axis) : run B b (x+step i)=run B b x+(if b.glare i then -step i else step i) := by
  have he := Step.vec_rotate (R:=Per (Domain m B)) (posDir i) (glazed b.glare)
  unfold run affine; rw [Signed.act_add]; simp only [Step.vec_pos] at he; rw [←he]
  change _+(if _ then _ else _)+_=_; unfold posDir glazed Step.rotate; simp only [Bool.false_xor,Equiv.refl_apply]; abel
lemma invert_path (U : Skin m B) (k : Site (Domain m B)→E) : through B b (Lattice.gauge k U)=Lattice.gauge (k ∘ run B b) (through B b U) := by
  funext ⟨x,i⟩
  let p := (posDir i).rotate (glazed b.glare)
  have he : run B b (x+step i)=run B b x+p.vec := by rw [step_plane]; apply congrArg; unfold p Step.vec; cases h:b.glare i <;> simp [Step.rotate, posDir,glazed,h]
  change Step.read p (Lattice.gauge k U) _= k (run B b x)*p.read U (run B b x)*(k (run B b (x+step i)))⁻¹
  rw [he]; exact Step.gauge_read ..
lemma through_guard {U : Skin m B} {e : ℝ} (h : Guard U e) : Guard (through B b U) e := by
  have he {I : Type} [Fintype I] [DecidableEq I] (R : E →* UNI I) (k : PlaqBound R U e) : PlaqBound R (through B b U) e := by
    intro x i j l
    let P := fun g:E=>‖(R g).val-1‖
    let y := (posDir i).rotate (glazed b.glare); let z := (posDir j).rotate (glazed b.glare)
    have hp g : P g⁻¹=P g := by
      unfold P; rw [map_inv]; change ‖star _-_‖=_; rw [← star_one (R:=Op I), ←star_sub, norm_star,star_one]
    have hC g u : P (u*g*u⁻¹)=P g := by
      unfold P; rw [map_mul, map_inv,map_mul]; change ‖(R u).val*(R g).val*star (R u).val-1‖= _; rw [←twist_formula, show twist (R u) _-1=twist (R u) ((R g).val-1) by rw [map_sub,map_one],twist_norm]
    change P _≤ e; unfold through; rw [travel_pull, show List.map _ (square i j)= Lattice.oriented y z by
      unfold square Lattice.oriented; simp only [List.map_cons,List.map_nil,←Step.rev_pos,Step.rev_rotate]; rfl, price_shift_pos P U hp hC]; exact k _ i j l
  exact ⟨he _ h.1,he _ h.2⟩
lemma odd_rule (i : Axis) (x : Index m) : OddAxis m (adv b x i) ↔ OddAxis m (x i) := by
  let F := fun x: Index m => (assembly (More m)).residue x
  have he (x:Index m) : OddAxis m (x i) ↔ F x i=1 := Iff.rfl
  rw [he,he]; unfold F adv affine; rw [map_add,show (assembly (More m)).residue b.paneShift=0 from Ratio.residue_embed ..,add_zero]
  cases l:b.glare i
  · have hp : ((glazed b.glare).act x) i=x i := by simp [l]
    rw [←show OddAxis m (((glazed b.glare).act x) i) ↔ _ from he _,hp,he]
  have hp : ((glazed b.glare).act x) i= -x i := by simp [l]
  have hg : F ((glazed b.glare).act x) i= -(F x i) := by
    have hC : F (-x) = -F x := map_neg _ _
    rw [show -(F x i)=(-F x) i from rfl,←hC]; unfold F; apply congrArg (fun z: Per (GridN m)=> F (fun _=>z) i) hp
  change F _ i = 1↔F _ i=1; rw [hg]; exact (show ∀ p:ZMod 2,-p=1↔p=1 by decide) _
lemma span_act (x y : Site (Domain m B)) : separation (run B b x) (run B b y)=separation x y := by unfold run affine; rw [separation_translate,separation_signed]
lemma tilt (x y : Index m) (i : Axis) : delta1 (GridN m) (b.adv x i) (b.adv y i)=delta1 (GridN m) (x i) (y i) := by
  unfold adv affine delta1; cases g:b.glare i <;> simp only [Pi.add_apply,glaz,g,ite_true,ite_false,Bool.false_eq_true,add_sub_add_right_eq_sub]
  rw [show -(x i)- -(y i)= -(x i-y i) by abel,ZMod.natAbs_valMinAbs_neg]
lemma level (x y : Site (Domain m B)) (i : Axis) : delta1 (Domain m B) (run B b x i) (run B b y i)=delta1 (Domain m B) (x i) (y i) := by
  unfold run affine delta1; cases g:b.glare i <;> simp only [Pi.add_apply,glaz,g,ite_true,ite_false,Bool.false_eq_true,add_sub_add_right_eq_sub]
  rw [show -(x i)- -(y i)= -(x i-y i) by abel,ZMod.natAbs_valMinAbs_neg]
lemma roomA (x : Index m) (z : Site (Domain m B)) : run B b z∈room m B (adv b x) ↔ z∈room m B x := by
  have ht (y:Index m) (u:Site (Domain m B)) (i) : roomX m B (y i) (u i) ↔ delta1 _ (u i) ((address m B y) i)≤broadface m B (y i) := by rw [address,high_here]; rfl
  rw [room_mem,room_mem]; simp_rw [ht,addressAdv,b.level]; apply forall_congr'; intro i; by_cases g:OddAxis m (x i) <;> simp [broadface,b.odd_rule,g]
lemma fits (x y : Index m) : Fits m (adv b x) (adv b y) ↔ Fits m x y := by
  have he (i:Axis) : adv b x i=adv b y i ↔ x i=y i := by unfold adv affine; cases g:b.glare i <;> simp [g]
  unfold Fits; simp only [tilt,odd_rule,he]
lemma setN (S : Support (Domain m B)) (U V : Skin m B) (h : Agrees ↑(S.image (run B b)) U V) : Agrees S (through B b U) (through B b V) := by
  rintro ⟨x,i⟩ g e; have ha := mem_image_of_mem (run B b) g; have ht := mem_image_of_mem (run B b) e
  change _∈ _ at ha; change run B b (x+step i)∈ _ at ht; rw [step_plane] at ht
  have hh (U : Skin m B) : through B b U (x,i)=if b.glare i then (U (run B b x-step i,i))⁻¹ else U (run B b x,i) := by
    unfold through; change Step.read _ _ _=_; cases g:b.glare i <;> simp [Step.read,Step.used,g,glazed,posDir,Step.rotate]; rfl; rfl
  rw [hh,hh]; split <;> rename_i l
  · simp only [l,ite_true] at ht; rw [← sub_eq_add_neg] at ht; exact congrArg (·⁻¹) (h _ ht (show run B b x-step i+step i ∈ _ by rw [sub_add_cancel]; exact ha))
  simp only [l,ite_false] at ht; exact h _ ha ht
lemma room_run (x : Index m) : (room m B x).image (run B b)=room m B (adv b x) := by
  ext i; rw [mem_image]
  constructor; rintro ⟨v,h,rfl⟩; exact (roomA b x v).mpr h
  intro h; exact ⟨run B b⁻¹ i,(roomA b x _).mp (by rw [run_last]; exact h),run_last ..⟩
lemma courses (B) : Continuous (through B b) := by
  refine continuous_pi (fun ⟨x,i⟩=>?_); unfold through Lattice.pull Step.read; split <;> fun_prop -- tune
lemma covo : Continuous (oncue b) := continuous_pi (fun i=> continuous_apply (b.adv i))
lemma convey (B) : Continuous (onPack B b) := (show Continuous _ from ((courses b B).comp (continuous_fst (Y:=Cue m))).prodMk (b.covo.comp continuous_snd))
end YM.CF.Mir.Trip
