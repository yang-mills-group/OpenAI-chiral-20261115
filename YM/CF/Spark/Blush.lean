import YM.CF.Nova.Rune
import YM.CF.Ave.Home
/-! Modifying the regulator weight along SAME seam/frame/all matter. The
new plaquette weights use true clipped RGB launch expression. This checks RP
property along already supplied grid glazes. Grand normalization separately.
No smoothness claims for perturbative scales here. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spark
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Branch Vale MeasureTheory RG Wilson WilsonStartup RP Nova
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace
variable {n m B: Side} (p:Clip)
local notation "G0"=>SU.group
local notation "n'"=> Domain m B
local notation "F'"=> Face (Per n)
local notation "U0"=> Pack m B
local notation "A₁"=>E₁ m B
-- absorb plaquette weights on pack. including Sharp via smoothing penalty preserving stitch
variable (s:Signed)(u:Config G0 n)
def voice(x:ℝ)(f: SU.group.El):= max 0 (SU.group.chord f-x)
def tollX (x:ℝ)(u:Config G0 n):= ∑ i:F', voice x (faceValue u i)
lemma tc(x:ℝ):Continuous (fun u:Config G0 n=>tollX x u):=continuous_finsetSum _ fun i _=> continuous_const.max ((SU.group.continuous_chord.comp (continuous_travel ..)).sub continuous_const)
lemma toll_pos (x:ℝ):0 ≤ tollX x u:= sum_nonneg fun i _=> le_max_left ..
lemma toll_g(g)(x:ℝ):tollX x (Lattice.gauge g u)=tollX x u:=by simp [tollX,voice,Gauge.chord_conj]
lemma pull_toll (x:ℝ)(y:Site n):tollX x (pull s y u)=tollX x u:=by
 unfold tollX voice; simp_rw [Face.send_price u _ _ y SU.group.chord SU.group.chord_inv (fun k g=>SU.group.chord_conj g k)]; exact Equiv.sum_comp (Equiv.ofBijective _ ⟨Face.injective_send s y, Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩) (fun i:F'=>voice x (faceValue u i)) -- explicit
lemma tolled (x:ℝ): tollX x u=0 ↔ u∈Calm G0 n x:=by
 unfold tollX voice; rw [sum_eq_zero_iff_of_nonneg (fun i _=>le_max_left ..)]; simp only [mem_univ,forall_const]; constructor
 · intro h; change flags x u=∅; apply eq_empty_iff_forall_notMem.mpr; intro i hb; obtain ⟨p,t,k⟩:= (flags_spec ..).mp hb; exact (ne_of_gt (lt_of_lt_of_le (sub_pos.mpr k) (le_max_right ..))) (h p)
 intro h i; apply max_eq_left; apply sub_nonpos.mpr; by_contra g; have he:= lt_of_not_ge g; have hx:i.1∈flags x u:= (flags_spec ..).mpr ⟨i,anchor_visit i,he⟩; rw [show flags x u=∅ from h] at hx; simp at hx
lemma pull_basic(t: Site n):basicP p (pull s t u)=basicP p u:=by
 have ht(u:Config G0 n) : Vale.ren p (pull s t u)=Vale.ren p u:=by
    unfold Vale.ren; rw [energy_pull u]; simp_rw [← residual_send]; congr 1; exact Equiv.sum_comp (Equiv.ofBijective _ ⟨Face.injective_send s t, Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩) (fun v:F'=> Design.bulk p*WilsonStartup.residual G0 v u)
 unfold basicP; rw [ht,← Reef.echo_p,ht]
lemma bg (v:Site n→SU.group.El):basicP p (Lattice.gauge v u)=basicP p u:=by
 have hf:Lattice.gauge (Reef.echo v) (Reef.echo u)= Reef.echo (Lattice.gauge v u):=by funext i; simp [Lattice.gauge,Reef.echo]
 have h(u:Config G0 n)(v):Vale.ren p (Lattice.gauge v u)=Vale.ren p u:=by simp [Vale.ren,energy_gauge,WilsonStartup.residual,surplus_conjugate]
 unfold basicP; rw [←hf,h,h]
-- splitting smooth costs
lemma braid (i:Axis)(x y z:U0)(f: SU.group.El→ℝ) : let V v w:=∑ a: Face (Per n'), f (faceValue (tiedK m B i x v w).1 a); V y z+V z y=V y y+V z z :=by
 intro V; unfold V; rw [←sum_add_distrib,←sum_add_distrib]; refine sum_congr rfl ?_; rintro ⟨p,k⟩ _
 let M (x y' z') := (tiedK m B i x y' z').1; let l := square k.val.1 k.val.2; let E (y' z') := travel (M x y' z') p l
 change f (E y z)+f (E z y)=f (E y y)+f (E z z)
 rcases stays p k.property.ne i with h|h
 · have he a b : E a b=E a a := travel_local p l _ _ (fun e h₁ h₂=> (strum i x a b a).gaugeS e (h _ h₁) (h _ h₂))
   rw [he y z,he z y]
 have he a b : E a b=E b b := travel_local p l _ _ (fun e h₁ h₂=> barter i x a b b e (h _ h₁) (h _ h₂)); rw [he y z,he z y,add_comm]
lemma renFace (F:SU.group.El→SU.group.El)(V W:Config G0 n)(q:∀ i:F',faceValue W i=F (faceValue V i)) : Vale.ren p W= (∑ i:F', (fun u=>SU.group.price (F u)-Design.bulk p*surplus (F u)) (faceValue V i)):=by unfold Vale.ren energy WilsonStartup.residual; simp_rw [q]; rw [sum_sub_distrib]
lemma econX(i:Axis)(x y z:U0): let V(a b):= basicP p (tiedK m B i x a b).1; V y z+V z y=V y y+ V z z:=by
 intro V; let K(u:SU.group.El):= SU.group.price u - Design.bulk p*surplus u
 let V₁:=fun (x:Config G0 n')=>Vale.ren p x; let W:=fun (x:Config G0 n')=>V₁ (Reef.echo x); let A(u v):=(tiedK m B i x u v).1
 have h(y):V₁ y=∑ i:Face (Per n'), K (faceValue y i):=renFace p id y y fun _=>rfl
 have hp(y):W y=∑ i:Face (Per n'), K (Reef.qG (faceValue y i)):=renFace p Reef.qG y _ fun _=>Reef.echo_t ..
 have he: V₁ (A y z)+ V₁ (A z y)= V₁ (A y y)+ V₁ (A z z):=by simp_rw [h]; exact braid i x y z K
 have ht:W (A y z)+W (A z y)=W (A y y)+W (A z z):=by simp_rw [hp]; exact braid i x y z (K ∘ Reef.qG)
 have hi(y z):V y z= (V₁ (A y z)+W (A y z))/2:=rfl
 rw [hi,hi,hi,hi]; linarith
lemma prim_g (i)(T S:ℝ): primal p n T S (Lattice.gauge i u)=primal p n T S u:=by
 unfold primal; by_cases h:u∈ Calm G0 n S
 · rw [Set.indicator_of_mem h,Set.indicator_of_mem (show Lattice.gauge i u∈ Calm G0 n S from (tolled ..).mp (by rw [toll_g]; exact (tolled u S).mpr h)),bg]
 rw [Set.indicator_of_notMem h,Set.indicator_of_notMem]; intro g; apply h; apply (tolled ..).mp; rw [←toll_g u i]; exact (tolled ..).mpr g
end YM.CF.Spark
