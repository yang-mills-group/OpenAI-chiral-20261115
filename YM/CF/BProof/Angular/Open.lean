import YM.CF.BProof.Angular.Stage

/-! Framed template of eq:B-blend and the explicitly enumerated terms in the open Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Mag CF.BProof.Face SU MeasureTheory Wilson Set Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group

/-- parameters including dyadic, common across bands and gaps. -/
structure Hall (s : Side) where
  X : Design
  K : Chart G
  c : Side
  g : Ratio c s
  k : ℕ

variable {s : Side} (a x : Per s)(l:ℕ)(y:ℝ)(S:Hall s)(U:Config G s)(b: Eyes s)

/-- also used for multiplied bound terms. -/
def angle (d:ℕ) : ℝ := max 0 (min (2*(d:ℝ)/(l:ℝ)-1/2) 1)
lemma angle_mem (d:ℕ) : angle l d∈Set.Icc (0:ℝ) 1:=⟨le_max_left ..,max_le zero_le_one (min_le_right ..)⟩
lemma angle_zero (hl:0<l) {d:ℕ}(h:d*4≤l): angle l d=0:=by
 have ht:0<(l:ℝ):=Nat.cast_pos.mpr hl; have he:(d:ℝ)*4≤(l:ℝ):=by exact_mod_cast h
 unfold angle; apply max_eq_left; exact le_trans (min_le_left ..) (sub_nonpos.mpr ((div_le_iff₀ ht).mpr (by linarith)))
lemma angle_one (hl:0<l) {d:ℕ}(h:l*3≤d*4): angle l d=1:=by
 have ht:0<(l:ℝ):=Nat.cast_pos.mpr hl; have he:(l:ℝ)*3≤(d:ℝ)*4:=by exact_mod_cast h
 unfold angle; rw [min_eq_right,max_eq_right]; exact zero_le_one; apply (le_sub_iff_add_le).mpr; rw [le_div_iff₀ ht]; linarith
lemma angle_hop (hl:0<l) (d:ℕ): |angle l d-angle l (d+1)|≤2/(l:ℝ):=by
 set b:= 2*(d:ℝ)/(l:ℝ)-1/2; set c:= 2/(l:ℝ); have h:0≤c:=by unfold c; positivity
 have he:angle l (d+1)=max 0 (min (b+c) 1):=by unfold angle; push_cast; congr! 2; unfold b c; ring
 rw [he]; change |max 0 (min b 1)-_|≤c; apply (abs_max_sub_max_le_max ..).trans; refine max_le (by simpa using h) ((abs_min_sub_min_le_max ..).trans ?_); simp; exact le_of_eq (abs_of_nonneg h)

def inlet (i:Bool) := sheet U (front a l i)
def lifts := ∀ i:Bool,Lift S.K y (inlet a l U i) (b i)
/-- combine smoothed face frames and given labels. -/
def sight : Eyes s:=fun i=> smooth S.g S.X S.k (inlet a l U i) (b i)
/-- frame gauge for the whole band. -/
def V := stage a l U (sight a l S U b)
def hall := Lattice.gauge (V a l S U b) U
def outlook (i:Bool):= react (sight a l S U b i) (inlet a l U i)
def light : CF.BProof.Face.Sheet s:= profile S.K (angle l (along a x)) (outlook a l S U b false) (outlook a l S U b true)
/-- template in common frames; everywhere including cut normal. -/
def formal (p:Bond s):E:= Fin.cases 1 (fun i=> light a (time p.1) l S U b (space p.1,i)) p.2
lemma normal_light (x:Per s)(p:Space s) : formal a l S U b (vert x p)=1:=rfl
@[simp] lemma horizontal_light (p:Space s)(i:TAxis) : formal a l S U b (horiz x p i)=light a x l S U b (p,i):=by
 simp only [formal,horiz,Fin.cases_succ,time_join,space_join]
lemma front_mem (i:Bool)(he:l<s.val): along a (front a l i)≤l:=by cases i; simp; rw [front_right,along_add _ he]
lemma local_inlet (i:Bool)(he:l<s.val) (W:Config G s)(h:Agrees (↑(strip a l)) U W) : inlet a l U i=inlet a l W i:=sheet_eq U a _ l h (front_mem a l i he)
lemma lifts_rot (t) : lifts a l y S U b ↔ lifts a l y S (Lattice.gauge t U) (b*(eye a l t)⁻¹):=by
 unfold lifts inlet; simp_rw [sheet_gauge]; exact forall_congr' fun i=> Lift.change ..
lemma sight_rot (t): sight a l S (Lattice.gauge t U) (b*(eye a l t)⁻¹)=sight a l S U b *(eye a l t)⁻¹ := by
 ext1 i; simp only [sight,Pi.inv_apply,Pi.mul_apply, inlet,sheet_gauge]; exact smooth_move S.g S.X S.k _ _ (eye a l t i)
lemma V_rot (t): V a l S (Lattice.gauge t U) (b*(eye a l t)⁻¹) = V a l S U b * t⁻¹:=by rw [V,V,sight_rot]; exact stage_rot ..
lemma formal_rot (t): formal a l S (Lattice.gauge t U) (b*(eye a l t)⁻¹)= formal a l S U b:=by
 have h(i:Bool): outlook a l S (Lattice.gauge t U) (b*(eye a l t)⁻¹) i=outlook a l S U b i:=by
   unfold outlook; rw [sight_rot]; simp only [Pi.mul_apply,Pi.inv_apply,inlet,sheet_gauge,← react_mul]; exact congrArg (fun u=>react u _) (inv_mul_cancel_right (sight a l S U b i) (eye a l t i))
 ext1 x; unfold formal light; rw [h,h]
lemma hall_rot (t): hall a l S (Lattice.gauge t U) (b*(eye a l t)⁻¹) = hall a l S U b := by unfold hall; rw [V_rot]; ext1 x; simp [Lattice.gauge,mul_assoc]
lemma hall_local (he:l+1<s.val)(W:Config G s)(h:Agrees (↑(strip a l)) U W) : Agrees ↑(strip a l) (hall a l S U b) (hall a l S W b):=by
 have e:sight a l S W b=sight a l S U b:= funext fun i=>congrArg (fun U:CF.BProof.Face.Sheet s=>smooth S.g S.X S.k U (b i)) (local_inlet a _ U i (by omega) W h).symm
 unfold hall V; rw [e]; have he:=stage_local a _ U (sight a l S U b) he W h; intro p hp hq; unfold Lattice.gauge; rw [he hp,he hq,h p hp hq]
lemma formal_local (he:l<s.val)(W:Config G s)(h:Agrees (↑(strip a l)) U W) : formal a l S U b=formal a l S W b:=by
 ext1 p; unfold formal light outlook sight; rw [local_inlet a _ U _ he W h,local_inlet a _ U _ he W h]

lemma sight_m : Measurable (Function.uncurry (sight a l S)):=by
 apply measurable_pi_lambda; intro i; apply (smooth_c S.g S.X S.k).comp (f:=fun p : Config G s × Eyes s => (inlet a l p.1 i,p.2 i)) -- tune
 unfold inlet; fun_prop
lemma V_m : Measurable (Function.uncurry (V a l S)) := (stage_m a l).measurable.comp (f:=fun p : Config G s × Eyes s=>(p.1,sight a l S p.1 p.2)) (measurable_fst.prodMk (sight_m a l S))
lemma hall_m : Measurable (Function.uncurry (hall a l S)):=by
 have he:=V_m a l S
 have hh : Continuous (Function.uncurry (@Lattice.gauge (Per s) E _ _ _)):=by unfold Lattice.gauge Function.uncurry; fun_prop
 exact hh.measurable.comp (f:=fun p : Config G s × Eyes s=>(V a l S p.1 p.2,p.1)) (he.prodMk measurable_fst)
lemma outlook_m (i:Bool): Measurable (Function.uncurry (fun U b=>outlook a l S U b i)):=by
 have h₁:Measurable (fun p : Config G s × Eyes s=> sight a l S p.1 p.2 i):= (measurable_pi_apply (X:=fun _ : Bool=> Frame s) i).comp (sight_m a l S)
 have h₂: Measurable (fun p: Config G s × Eyes s=> inlet a l p.1 i):=by unfold inlet; fun_prop
 exact (react_c (s:=s)).measurable.comp (f:=fun p : Config G s × Eyes s=>(sight a l S p.1 p.2 i,inlet a l p.1 i)) (h₁.prodMk h₂)
lemma light_m : Measurable (Function.uncurry (light a x l S)):= by
 change Measurable (Function.uncurry (profile (s:=s) S.K (angle l (along a x))) ∘ fun (p:Config G s × Eyes s)=> (outlook a l S p.1 p.2 false,outlook a l S p.1 p.2 true)) -- tune
 exact (profile_c S.K _).comp ((outlook_m a l S false).prodMk (outlook_m a l S true))
lemma formal_m : Measurable (Function.uncurry (formal a l S)):=by
 apply measurable_pi_lambda; intro p; rcases whichBond p with ⟨x,p,rfl⟩|⟨x,p,i,rfl⟩
 · unfold Function.uncurry; simp_rw [normal_light]; exact measurable_const
 unfold Function.uncurry; simp_rw [horizontal_light]; exact (measurable_pi_apply (X:=fun _ : Slat s=> E) (p,i)).comp (light_m a x l S)
end YM.CF.BProof.Angular
