import YM.CF.BPress.Sheet
/-! VolumeB-gate: frame sums in terms of site parameters. Need bijection of frames into new variables (in the same slice after gauge turns). At accepted faces, 0 or 5 choices; never assuming gratuitous lift/gauge equivariance of the choice. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Sheet.Atlas
open Function MeasureTheory Lattice SU Mag Cube Grid Filter Finset
open scoped Topology BigOperators Classical Matrix
variable {s : Side} (T : Atlas) (y : ℝ)
structure Coasts (T : Atlas) (y : ℝ) : Prop where
 pass : sigmaN y ≤ T.tube
 sep : sigmaN y + sigmaN y < T.narrow
lemma coasts_y : ∀ᶠ y in atTop,T.Coasts y:=
 ((npl_sigmaN.drop.eventually (ge_mem_nhds T.tunnel)).and ((npl_sigmaN.add npl_sigmaN).drop.eventually (gt_mem_nhds T.sep_pos))).mono fun y x=>⟨x.1,x.2⟩
variable (U : Horiz s) (h : T.Coasts y)

def room (U : Horiz s) : Finset (Law s):= univ.filter fun k=> T.allowed y U (T.frame y U k)
@[simp] lemma room_ok (l : Law s): l∈T.room y U↔ T.allowed y U (T.frame y U l):=by simp [room]

def seats := (T.room y U).image (T.frame y U)
variable {U}
include h in
lemma give_onto {x : Tri s}{a : E}(p:T.passes y U x)(g:Chosen (T.hue y U x) a): ∃ i, T.give y U x i=a:=by
 have ht : T.hue y U x∈Mood T.tube:= by obtain ⟨j,v⟩:=p.2; exact ⟨j,v.trans h.pass⟩
 obtain ⟨i,t⟩:= T.sheet _ ht _ _ (T.chosen _) g; exact ⟨i,t.symm⟩
include h in
lemma on_frame {x : HFrame s}(p:T.allowed y U x) : ∃ i∈T.room y U, T.frame y U i=x:=by
 choose φ g using fun i=> T.give_onto y h (p.1 i).1 (p.1 i).2; have ht: T.frame y U φ=x:= funext g; exact ⟨φ,(T.room_ok ..|>.mpr (ht.symm ▸ p)),ht⟩
include h in
lemma seats_ok {x : HFrame s} : x∈T.seats y U ↔ T.allowed y U x:=by
 rw [seats,mem_image]; refine ⟨?_, fun p=>T.on_frame y h p⟩; rintro ⟨i,v,rfl⟩; exact T.room_ok ..|>.mp v
lemma sep_given {x : Tri s} (l k : Law s)(p : l x≠k x) : T.narrow ≤ chord (T.frame y U l x) (T.frame y U k x):= by unfold frame give; rw [chord.right]; exact T.apart p
include h in
lemma story (x : FlatLink s) {l k : HFrame s}(a:T.allowed y U l)(b:T.allowed y U k)(t : l x.1=k x.1): l (hop x.1 x.2 1)=k (hop x.1 x.2 1):=by
 obtain ⟨i,hi,ei⟩:= T.on_frame y h a; obtain ⟨j,hj,ej⟩:= T.on_frame y h b
 let z:=hop x.1 x.2 1; by_cases p:i z=j z; exact (show l z=k z by rw [←ei,←ej]; simp only [frame,p])
 exfalso; apply not_lt_of_ge (T.sep_given y (U:=U) i j p); rw [ei,ej]; have ht:= chord.triangle (adjust l U x) 1 (adjust k U x); rw [chord.comm 1,chord.one,chord.one] at ht; apply lt_of_le_of_lt ?_ h.sep; refine (Eq.le ?_).trans (ht.trans (add_le_add (a.2 x) (b.2 x))); simp [adjust,t,z] -- tune
private lemma plane_all (p : Tri s → Prop) (x : Tri s)(h : p x)(v : ∀ x, p x→ ∀ i:SpatialDir, p (hop x i 1)): ∀ y,p y:=by
 have he(x:Tri s)(i:SpatialDir)(b:Per s)(t:p x) : p (update x i b):=by
    have g(k:ℕ): p (hop x i k):= by induction k with|zero=> simpa using t|succ k ih=>rw [←hop_hop]; exact v _ ih _
    have hel : hop x i (b-x i).val = update x i b:=by funext j; by_cases f:j=i<;> simp [hop_at,update,f, Per]
    rw [←hel]; apply g
 intro y; rw [show y=update (update (update x 0 (y 0)) 1 (y 1)) 2 (y 2) by funext i; fin_cases i<;>simp
    ]; exact he _ _ _ (he _ _ _ (he _ _ _ h))
include h in
lemma determined (x : Tri s) {l k : HFrame s} (p:T.allowed y U l)(q:T.allowed y U k)(f:l x=k x): l=k:= funext (plane_all (fun i=>l i=k i) x f fun x p' i=> T.story y h (x,i) p q p')
include h in
lemma room_unique (x : Tri s) {l k : Law s} (p:l∈T.room y U)(q:k∈T.room y U)(f : l x=k x) : l=k:=T.frame_inj y U (T.determined y h x (T.room_ok ..|>.mp p) (T.room_ok ..|>.mp q) (congrArg _ f)) -- tune
variable (U)
lemma seats_ceiling : (T.seats y U).card=(T.room y U).card:= card_image_of_injective _ (T.frame_inj ..)
include h in
lemma room_ceiling : (T.room y U).card≤5:=by
 rw [← Fintype.card_fin 5]; refine card_le_card_of_injOn (fun f:Law s=>f 0) (fun _ _=>mem_univ _) (fun i p j q f=>T.room_unique y h _ p q f)|>.trans_eq (card_univ)
include h in
lemma room_star5 (x : (T.room y U)) : (T.room y U).card=5:=by
 apply le_antisymm (T.room_ceiling y U h); let f : Fin 5 → HFrame s:= fun i=> (fun _=>center i) * (T.frame y U x.val); have hf : Injective f:=by intro i j e; exact center_injective (mul_right_cancel (congrFun e (0:Tri s)))
 rw [←T.seats_ceiling]; refine le_trans ?_ (card_le_card (t:=T.seats y U) (s:=univ.image f) ?_); rw [card_image_of_injective _ hf]; simp; intro i p; obtain ⟨j,_,rfl⟩:= mem_image.mp p; apply (T.seats_ok y h).mpr; exact T.allow_center y j (T.room_ok ..|>.mp x.property)
include h in
lemma seats_adj (a:HFrame s) : T.seats y (adjust a U)=(T.seats y U).image fun h=> h*a⁻¹:=by
 ext x; rw [T.seats_ok y h,mem_image]; constructor
 · intro p; refine ⟨x*a,(T.seats_ok y h).mpr ?_,mul_inv_cancel_right ..⟩; have he:= T.allow_g y a⁻¹ p; rw [inv_inv,adjust_seq,inv_mul_cancel,adjust_one] at he; exact he
 rintro ⟨i,p,rfl⟩; exact T.allow_g y a ((T.seats_ok y h).mp p)

-- sums used inside more than one function/Mark. Later Marks can use a joint sum over pairs of these.
variable {F : Type*} [AddCommMonoid F]
lemma sum_parameters (f : HFrame s→F) : ∑ i∈T.seats y U, f i=∑ i∈T.room y U,f (T.frame y U i):= sum_image (s:=T.room y U) (f:=f) fun i _ j _ e=>T.frame_inj _ U e
include h in
lemma sum_adjust (a : HFrame s)(f:HFrame s→ F): ∑ i∈T.seats y (adjust a U),f i=∑ i∈T.seats y U, f (i*a⁻¹):=by rw [T.seats_adj y U h]; exact sum_image fun i _ j _ e=> mul_right_cancel e
variable {M : Type*} [MeasurableSpace F] [MeasurableSpace M] [MeasurableAdd₂ F]
lemma sum_borel (x:M→Horiz s)(p:Measurable x)(f:M× HFrame s→F)(q:Measurable f): Measurable (fun c=> ∑ i∈T.seats y (x c), f (c,i)):=by
 simp_rw [T.sum_parameters]; simp only [room,sum_filter]; apply Finset.measurable_fun_sum; intro i _; have hx:= T.frame_meas y i|>.comp p; exact Measurable.ite (p.prodMk hx (T.allowed_meas y)) (q.comp (measurable_id.prodMk hx)) measurable_const
end YM.CF.BPress.Sheet.Atlas
