import YM.SU5.FiniteGaugeData.Marked.Variation.Hearth
/-! # Dictionary of finite-support Wide Families. Finite exterior basis on ANY sufficiently uncrowded torus. The canonical coefficients are common bounded Borel functions, no a.e. choices needed. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra

variable (K : Calibration) (S : Finset Cover)
variable {m N : Side}

abbrev Roomy (S : Finset Cover) (N : Side) := Hosp (tips S) N

lemma hosp_mono {S T : Finset Cover} (p : Hosp T N) (h : S ⊆ T) : Hosp S N :=
  ⟨p.seat_.mono h⟩
lemma roomy_hosp (h : Roomy S N) : Hosp S N := hosp_mono h (fun _ a=>tips_here S a)

/-- Copy a pair on the infinite cover into a finite location, ignoring which equivalent
value a priori is paid on the eventual election. -/
lemma graft_at (h : Hosp S N) (v : LinksC) {x : Cover} (p : x ∈ S) (i : Axis) :
    graft S N v (wrap (More N) x,i) = v (x,i) := by
  simpa only [onC_spec] using Satin.tail S N h v (x,i) p

/-- Copying preserves all *internal* edge coordinates, provided the wraps are hospitable
on the set and all outward positive step tips. No assertion for a support which already
wraps or takes all but one side of a torus. -/
lemma graft_agrees (h : Roomy S N) {v w : LinksC} (p : Agrees S v w) :
    Agrees (region S N) (graft S N v) (graft S N w) := by
  rintro ⟨x,i⟩ a b
  obtain ⟨y,u,rfl⟩:=mem_image.mp a; obtain ⟨z,g,zv⟩:=mem_image.mp b
  have hex:y+step i=z:= h.seat_ (tips_there S u i) (tips_here S g) (by rw [map_add,wrap_step]; exact zv.symm)
  rw [graft_at S (roomy_hosp S h) v u,graft_at S (roomy_hosp S h) w u]; exact p (y,i) u (hex.symm ▸ g)

lemma graft_preserves (h : Hosp S N) (v : Pane N) : Agrees (region S N) (graft S N (onC N v)) v := by
  rintro ⟨x,i⟩ a _; obtain ⟨y,u,rfl⟩:=mem_image.mp a
  rw [graft_at S h _ u, onC_spec]

lemma occupy_surj (h : Hosp S N) (i : Single N) (p : i ∈ modesIn N (region S N)) : ∃ a:Satin.Tag S, occupy S N h a=i := by
  obtain ⟨⟨x,g⟩,a⟩:=i
  rw [modes_at] at p
  obtain ⟨y,ys,e⟩:= mem_image.mp p
  change wrap (More N) y=node x at e
  let b:=nodeC (natural x)
  have hb: wrap (More N) y=wrap (More N) b:=by rw [e]; unfold b; rw [←node_of, Rush.nat_true]
  let d:= periods (More N) y-periods (More N) b
  have he:y = b + (More N).val • d:=by
    unfold d; have h1:=Rush.carrying (More N) y; have h2:=Rush.carrying (More N) b
    rw [hb] at h1; rw [smul_sub]
    grind
  let w:= natural x + N.val • d
  have hw:nodeC w=y := by
    unfold nodeC w; unfold b nodeC at he; rw [he]; rw [smul_add, smul_smul]; change _= (2:ℕ)•_+_+(N.val*2) • _; rw [Nat.mul_comm 2]; abel
  have hz: wrap N w=x := needle (by rw [node_of,hw]; exact e)
  exact ⟨⟨(w,g,a),hw.symm ▸ ys⟩, congrArg (fun w' => ((w',g),a)) hz⟩

abbrev Key := Evens S
abbrev Typeset (S : Finset Cover) (a : Key S) := tagWord S a.val

def turnScalar (h : Hosp S N) (a : Key S) := Classical.choose (museum S N h a.val)
lemma turn_weight (h : Hosp S N) (a : Key S) : ‖turnScalar S h a‖=1 := (Classical.choose_spec (museum S N h a.val)).1
lemma turn_nz (h : Hosp S N) (a : Key S) : turnScalar S h a≠0 := norm_pos_iff.mp (by rw [turn_weight]; exact zero_lt_one)

/-- Phase-aware Fourier-exterior coefficient selector. -/
def selector (h : Hosp S N) (a : Key S) : FC (Single N) →ₗ[ℂ] ℂ where
  toFun f := (turnScalar S h a)⁻¹ * crumb (twist (star (flake (Tset N)ᶜ)) f) (a.val.map (occupy S N h))
  map_add' f g := by rw [map_add, crumb, crumb, crumb,Matrix.add_apply,mul_add]
  map_smul' a t := by rw [twist_scalar,crumb_scale,RingHom.id_apply, smul_eq_mul]; ring

lemma selector_apply (h : Hosp S N) (a : Key S) (f : FC (Single N)) :
  selector S h a f= (turnScalar S h a)⁻¹ * crumb (twist (star (flake (Tset N)ᶜ)) f) (a.val.map (occupy S N h)) := rfl
lemma selector_n (h : Hosp S N) (a : Key S) (f : FC (Single N)) : ‖selector S h a f‖ ≤ ‖f‖ := by
  rw [selector_apply,norm_mul,norm_inv,turn_weight,inv_one,one_mul]; exact (norm_entry (twist (star (flake (Tset N)ᶜ)) f) (a.val.map (occupy S N h)) ∅).trans_eq (twist_norm ..)

lemma selector_spool (h : Hosp S N) (a b : Key S) [Decidable (a=b)] :
    selector S h a (spool N (tagWord S b.val)) = if a=b then 1 else 0 := by
  have he : spool N (tagWord S b.val)=(velvet S N).tag b.val:=by unfold Poly.tag spool; simp only [tagWord,List.map_map]; rfl
  rw [selector_apply, he, show twist _ _=_ from (Classical.choose_spec (museum S N h b.val)).2, crumb_scale, Pastry.chip]; split_ifs with u v w
  · subst b; rw [mul_one]; exact inv_mul_cancel₀ (turn_nz S h a)
  · exact False.elim (v (Subtype.ext (Finset.map_injective (occupy S N h) u)))
  · subst b; simp at u
  simp

private lemma letter_of_think (h : Hosp S N) (a : Satin.Tag S) : ∃ c:ℂ,
    (Reed.think (Tset N)).term (occupy S N h a) = c • Satin.thread N (stock S a) := by
  obtain ⟨⟨x,i,j⟩,p⟩:=a
  let q:= Lifted.index N x i j; let w:= Lifted.winding N x; have hw:w≠0:=norm_pos_iff.mp (by change 0<‖Rush.fee _‖; rw [Rush.fee_norm]; exact zero_lt_one)
  change ∃ c:ℂ, (Reed.think (Tset N)).term q=c • Satin.thread N (x,i,j)
  by_cases t:i∈plusHalf
  · refine ⟨w⁻¹,?_⟩; rw [show (Reed.think (Tset N)).term q=put q from if_pos ((mem_Tset ..).mpr t)]
    unfold Satin.thread; rw [if_pos (show i∈ plusHalf from t)]; simp only [basisC, map_smul, create_put]; exact (inv_smul_smul₀ hw _).symm
  refine ⟨-(star w)⁻¹,?_⟩; rw [show (Reed.think (Tset N)).term q= -takeF q from if_neg (fun ht=> t ((mem_Tset ..).mp ht)), Satin.thread,if_neg (show ¬i∈ plusHalf from t)]; simp only [basisC,Fock.remove, map_smul, create_put,star_smul]; change -takeF q= -(star w)⁻¹ • (star w • takeF q); rw [neg_smul, inv_smul_smul₀ (by simpa using hw : star w ≠ 0)]
private lemma realize_const (h : Hosp S (K.c m)) {b : Bool} {v : FC (Single (K.c m))} (p : Fine (Tset _) (modesIn _ (region S (K.c m))) b v) :
    ∃ f: Family K, InTest K true S b f ∧ ∀ x, f m x = v := by
  induction p with
  | empty => exact ⟨0,.zero,fun _=> rfl⟩
  | one => exact ⟨1,.one,fun _=>rfl⟩
  | seed i p =>
    obtain ⟨a,rfl⟩:= occupy_surj S h i p
    obtain ⟨c,e⟩:=letter_of_think S h a
    have hv:InTest K true S true (Sound.chord K (stock S a)):= chord_t K _ (show {a: Blot//nodeC a.1∈S} from a).property
    refine ⟨c • Sound.chord K (stock S a),.smul _ hv,fun _=>?_⟩; rw [e, Pi.smul_apply,Pi.smul_apply]; unfold Sound.chord Satin.thread; split<;>rfl
  | add _ _ ih hk=> obtain ⟨f,t,v⟩:= ih; obtain ⟨g,u,z⟩:=hk; exact ⟨f+g,t.add u,fun x=>congrArg₂ (·+·) (v x) (z x)⟩
  | grow _ _ ih hk=> obtain ⟨f,t,v⟩:= ih; obtain ⟨g,u,z⟩:=hk; exact ⟨f*g,t.mul u,fun x=>congrArg₂ (·*·) (v x) (z x)⟩
  | scale _ c ih=> obtain ⟨f,u,z⟩:=ih; exact ⟨c • f, .smul _ u,fun x=> congrArg (fun u=>c • u) (z x)⟩

/-- Synthesis written on PairsC. -/
abbrev Score (S : Finset Cover) := Key S → PairsC → ℂ
def composeLetters (f : Score S) : Family K := ∑ a:Key S, note K (f a) (Typeset S a)
lemma letters_apply (f : Score S) (m : Side) (x) :
    composeLetters K S f m x=∑ a:Key S, f a (Prod.map (onC _) (onC _) x) • spool (K.c m) (Typeset S a) := by
  unfold composeLetters; simp_rw [Finset.sum_apply, note_v, spool_sing]
lemma letters_t (f : Score S) (p : ∀ a,Coeff true S (f a)) : InTest K true S false (composeLetters K S f) := InTest.sum _ _ (fun a _=> a.property ▸ note_t K (tagWord S a.val) (p a) (brand S a.val))
lemma letters_zero : composeLetters K S 0=0 := by
  funext m x; rw [letters_apply]; simp
lemma letters_more (f g : Score S) : composeLetters K S (f+g)= composeLetters K S f+ composeLetters K S g:=by
  funext m x; simp_rw [Pi.add_apply,letters_apply,Pi.add_apply,add_smul,sum_add_distrib]
lemma letters_scalar (f : Score S)(a:ℂ) : composeLetters K S (a • f)= a • composeLetters K S f:=by
  funext m x; simp_rw [Pi.smul_apply, letters_apply, Pi.smul_apply, smul_sum, smul_eq_mul, smul_smul]
lemma selector_letters (h : Hosp S (K.c m))(a : Key S)(f : Score S) (X) :
    selector S h a (composeLetters K S f m X)= f a (Prod.map (onC _) (onC _) X) := by
  classical
  rw [letters_apply,map_sum]; simp_rw [map_smul,Typeset,selector_spool]
  simp

lemma analyze (h : Hosp S (K.c m)) {v : FC (Single (K.c m))} (p : Fine (Tset _) (modesIn _ (region S (K.c m))) false v) :
    (∑ a:Key S, selector S h a v • spool (K.c m) (Typeset S a)) = v := by
  obtain ⟨f,g,u⟩:=realize_const K S h p
  obtain ⟨a,e⟩:=circulation S K g
  let k:Score S:= fun i=>(a i).val; change f=composeLetters K S k at e
  rw [←u (1,1),e]; simp_rw [selector_letters]; exact (letters_apply ..).symm

def takeScore (h : Hosp S N) (f : Mark N) : Score S := fun a x=> selector S h a (f (replant S _ x))
lemma takeScore_zero (h : Hosp S N) : takeScore S h 0=0 := funext fun _=>funext fun _=> map_zero _
lemma takeScore_more (h : Hosp S N) (f g : Mark N) : takeScore S h (f+g)=takeScore S h f + takeScore S h g := funext fun _=> funext fun _=> map_add _ _ _
lemma takeScore_scalar (h : Hosp S N) (f : Mark N)(a:ℂ) : takeScore S h (a • f)=a • takeScore S h f:= funext fun i=>funext fun x=> map_smul (selector S h i) a (f (replant S N x))
lemma take_coeff (h : Roomy S N){f:Mark N}(p:AtSupport false (region S N) f)(a:Key S) : Coeff true S (takeScore S (roomy_hosp S h) f a) := by
  let Z := selector S (roomy_hosp S h) a
  refine ⟨fun _=> by contradiction,Girt.pole_w _ Z Z.continuous_of_finiteDimensional (Env.along p.env (replant_b ..)),?_⟩
  intro x y u v; exact congrArg Z (p.dep (replant S N x) (replant S N y) (graft_agrees S h u) (graft_agrees S h v))

lemma take_letters (h : Hosp S (K.c m)) (f : Score S) (p :∀ a,Coeff true S (f a)) :
    takeScore S h (composeLetters K S f m)= f := by
  funext a x; unfold takeScore; rw [selector_letters]; apply (p a).locus <;> exact fun i has _=>Satin.tail S _ h _ i has
lemma letters_take (h : Hosp S (K.c m)) {f : Mark (K.c m)} (p : AtSupport false (region S (K.c m)) f) :
    composeLetters K S (takeScore S h f) m=f:=by
  funext x; rw [letters_apply]; unfold takeScore
  have he:f (replant S _ (Prod.map (onC _) (onC _) x))= f x:= p.dep _ _ (graft_preserves S h _) (graft_preserves S h _)
  simp_rw [he]; exact analyze K S h (p.allV _)
lemma letters_restore (h : Hosp S (K.c m)) {F : Family K} (p : InTest K true S false F) :
    composeLetters K S (takeScore S h (F m)) = F:=by
  obtain ⟨a,v⟩:=circulation S K p; change F= composeLetters K S (fun i=>(a i).val) at v; rw [v,take_letters K S h _ fun i=>(a i).property]
lemma take_family (h : Hosp S (K.c m)) {F : Family K} (p : InTest K true S false F) (a:Key S):
    Coeff true S (takeScore S h (F m) a) := by
  obtain ⟨z,v⟩:=circulation S K p; change F=composeLetters K S (fun i=>(z i).val) at v; rw [v,take_letters K S h _ fun i=>(z i).property]; exact (z a).property

lemma family_eq (h : Hosp S (K.c m)){f g : Family K}(p:InTest K true S false f)(t:InTest K true S false g)(v:f m=g m): f=g:= by
  exact (letters_restore K S h p).symm.trans ((congrArg (fun f=> composeLetters K S (takeScore S h f)) v).trans (letters_restore K S h t))
#print axioms letters_take
#print axioms family_eq
end YM.CF.Buffered.Afterglow.Hierarchy
