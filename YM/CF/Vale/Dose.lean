import YM.CF.Vale.Palm
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom PhysicalNext.JointLoad.Heir
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v i:ℕ}{f g a b d w:ℝ}{B m c u:Side}{C:Credit}
variable {U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}{S:Gold K P R W}{x y z:ℝ}
section wages
variable (A:S.Last D C m v)
lemma vent (L:ℝ→ℝ)(z:ℝ) (hp:Continuous L)(a b:ℝ)(h:a ≤ b)(hx:L a ≤ z)(hy:z≤L b): ∃ x∈ Set.Icc a b,L x=z:=by
 obtain ⟨x,h,hP⟩:= intermediate_value_Icc h hp.continuousOn (show z∈Set.Icc (L a) (L b) from ⟨hx,hy⟩); exact ⟨x,h,hP⟩
abbrev Gold.Last.Running (q:ℕ→ℝ):Prop:=∀ i, i<v → |q i - (q (i+1) + (S.charge (v-1-i)+A.shift i))| ≤ 1
def Gold.Last.music (A:S.Last D C m v)(X:ℝ):Prop:=∀ (i j:ℕ),i+j≤v→ |(∑ w∈range j,A.shift (i+w))- (j:ℝ)*billC P.L| ≤ X
lemma spark {A:S.Last D C m v}{q:ℕ→ℝ}(h:A.Running q)(p:A.music x)(l t:ℕ)(hp:l+t≤ v): |q (l+t)-q l - t*net P.L| ≤ (t:ℝ)*K.top.drift+x:=by
 have he(j:ℕ)(u:j≤t): |q (l+j) - q l-(j:ℝ)*billX P.L+(∑ i∈range j,A.shift (l+i))| ≤ j*K.top.drift:=by
    induction j with
    | zero=>simp
    | succ j ih=>
        let i:=l+j; let e:=v-1-i; let W:=q (i+1)+S.charge e+A.shift i-q i
        have hh:= h i (by unfold i; omega); have hQ:|W|≤1:=by unfold W e; rw [← add_assoc] at hh; rwa [abs_sub_comm]
        have ht:|W-(S.charge e+billX P.L)| ≤ K.top.drift:= (abs_sub _ _).trans ((add_le_add_left hQ _).trans (?_)) -- left addition goal
        · rw [Nat.cast_add,Nat.cast_one,sum_range_succ]; rw [show q _ - q l- (j+1:ℝ)*billX P.L+ (_+_)= q i-q l-j*billX P.L+(∑ i∈range j,A.shift (l+i))+(W-(S.charge e+billX P.L)) from ?_]; exact (abs_add_le ..).trans ((add_le_add (ih (by omega)) ht).trans_eq (by ring)); unfold W i e; rw [← Nat.add_assoc]; abel_nf
          ring
        rw [add_comm]; exact S.bound e
 let X:= (∑ i∈range t,A.shift (l+i)); have hy : |q (l+t)-q l-t*net P.L| = |q (l+t)-q l-t*billX P.L+X-(X-t*billC P.L)|:=by unfold net; ring_nf
 rw [hy]; exact (abs_sub ..).trans (add_le_add (he t le_rfl) (p l t hp))
def room (d:ℝ)(L:Side):Prop:= billX L*(3/4:ℝ)≤ net L-d ∧ net L+d ≤ billX L*(5/4:ℝ)
lemma clearance (C:ℝ)(p:0≤ C):∃ n:ℕ,∀ L:Side,n≤L.val→ room C L:=by
 have hA : 3/4*group.slopeConstant< group.slopeConstant-spiceM:=by
    unfold Gauge.slopeConstant spiceM; rw [hut_k]; have hx:= Real.pi_pos; field_simp; norm_num
 have h':(group.slopeConstant-spiceM)< (5/4:ℝ)*group.slopeConstant:=by linarith only [Gauge.slopeConstant_pos yet_one,(show 0<spiceM by unfold spiceM; positivity)]
 let A:=group.slopeConstant-spiceM; let a:=min (A-3/4*group.slopeConstant) ((5/4:ℝ)*group.slopeConstant-A)
 have he:0<a:=lt_min (sub_pos.mpr hA) (sub_pos.mpr h'); obtain ⟨n,X⟩:=eventually_atTop.mp ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop)).eventually_ge_atTop (C/a))
 refine ⟨n,fun L hn=>?_⟩; let f:=Real.log L.val; have hx:f ≥ C/a:= X L.val hn; have hu:0≤ f:= (div_nonneg p he.le).trans hx
 unfold room net billX billC; apply And.intro <;> nlinarith only [mul_le_mul_of_nonneg_right (show a ≤ A - 3/4*group.slopeConstant from min_le_left ..) hu, mul_le_mul_of_nonneg_right (show a ≤ (5/4:ℝ)*group.slopeConstant-A from min_le_right ..) hu, (div_le_iff₀ he).mp hx] -- unfold A
-- shoot with arbitrary clamped RG trials generated later. ±1 increment
structure Arcs (A:S.Last D C m v)(F:ℕ→ℝ→ℝ) :Prop where
 top:F v=id
 core(i:ℕ)(t:i≤v): Continuous (F i)
 fp (s:ℝ): A.Running (fun i=> F i s)
def matchedX (b p :ℝ):Prop:= b/2 ≤ p∧ p ≤ 2*b
lemma reach {A:S.Last D C m v}{F:ℕ→ℝ→ℝ} (P':Arcs A F)(h:A.music z)(u:2*z ≤ x)(t:0≤x)(r:room K.top.drift P.L)(w:0≤z): ∃ a:ℝ,F 0 a=x ∧ ∀ i,i≤v → matchedX (hat P.L x i) (F i a) :=by
 let b:=x+v*net P.L; let d:ℝ:= v*K.top.drift+z
 have hz:0≤d:=add_nonneg (mul_nonneg (by positivity) K.top.drift_ge) w
 have hp(y:ℝ): |y-F 0 y-v*net P.L| ≤ d:=by
    have he:=spark (P'.fp y) h 0 v (by omega); rw [Nat.zero_add,P'.top] at he; exact he
 obtain ⟨a,-,Z⟩:= vent (F 0) x (P'.core 0 (by omega)) (b-d) (b+d) (by linarith) (by linarith [(abs_le.mp (hp (b-d))).1]) (by linarith [(abs_le.mp (hp (b+d))).2])
 refine ⟨a,Z,fun i hi=>?_⟩; have he:= spark (P'.fp a) h 0 i (by omega); rw [Z,Nat.zero_add] at he
 obtain ⟨hQ,hV⟩:= abs_le.mp he; obtain ⟨r,R⟩:= r; unfold matchedX hat; constructor <;> nlinarith [mul_nonneg (a:=(i:ℝ)) (by positivity) (pitch P.L)]
end wages
end YM.CF.Vale
