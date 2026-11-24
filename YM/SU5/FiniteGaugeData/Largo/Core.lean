import YM.SU5.FiniteGaugeData.Largo.Prill
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side} {b:Bool}{D l n:ℕ}{α C:ℝ}{v:ℝ} {i j:ℕ}
lemma instant_pay {i:ℕ} (h:i<D):-((l+D:ℕ):ℤ) ≤ instant l b i∧instant l b i ≤ ((l+D:ℕ):ℤ):=by rw [floorInst]; cases b<;> simp <;> omega -- annotation
lemma wrap_d (u v:ℤ)(p:((u:Per N)=v))(hp:(u-v).natAbs < N.val) : u=v:=by
 have he: (N.val:ℤ)∣v-u:= (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp p; have hh: (v-u).natAbs < (N.val:ℤ).natAbs := by omega; -- tune abs
 exact Eq.symm (sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs he hh))
lemma instant_eq (h:i<D)(t:j<D)(g:l+D+l+D < N.val) : ((instant l b i:Per N)=instant l b j) ↔ i=j:= ⟨fun p=>floorMono _ _ (wrap_d _ _ p (by have he:=instant_pay (b:=b) (l:=l) h; have hx:=instant_pay (b:=b) (l:=l) t; omega)), fun v=> by rw [v]⟩
namespace Limit
variable {o:Rim}{x y:Fin n→ Flight}{K:Flight→Flight→ℂ} (h:Limit n D x y K)
include h
lemma fertile : Injective x:= by intro i j p; by_contra t; exact (Matrix.isUnit_iff_isUnit_det _ |>.mp h.rank).ne_zero (Matrix.det_zero_of_row_eq t (by ext z; simp [p]))
lemma ferris : Injective y:= by intro i j p; by_contra t; exact (Matrix.isUnit_iff_isUnit_det _ |>.mp h.rank).ne_zero (Matrix.det_zero_of_column_eq t fun k=>by simp [p])
end Limit
def Whist(N:Side)(l D:ℕ)(b:Bool): Finset (Per N):= (Finset.range D).image fun i=> ((instant l b i):Per N)
abbrev seats (N:Side)(l D:ℕ)(b:Bool): Finset (Mini N):= clock (Whist N l D b)
abbrev Pavilion (N:Side)(l D:ℕ)(b:Bool): Finset (Mini N):= (seats N l D b) ∩ ruddy N
abbrev TerraceG (N:Side)(l D:ℕ)(b:Bool): Finset (Mini N):= (seats N l D b) ∩ scel N
lemma seatsE : seats N l D b⊆ Aeons N (l+D):= by
 intro i p; simp only [seats,clock,mem_filter, mem_univ,true_and, Whist,mem_image,mem_range] at p; obtain ⟨x,y,v⟩:=p; exact (Aeons_mem ..).mpr ⟨_,v,instant_pay y⟩
lemma PavilionE : Pavilion N l D b⊆ Aeons N (l+D):= Finset.inter_subset_left.trans seatsE -- tune
lemma terraceE : TerraceG N l D b⊆ Aeons N (l+D):= Finset.inter_subset_left.trans seatsE -- tune
abbrev boxSeats (l D:ℕ)(M:Tulip.Male)(N:Side)(b:Bool)(Q: Finset (Stereo N))(n:ℕ):= ∀ i:Q, ∃ x y:Fin n→ Flight, Limit n D x y (loan (berth (badge i.val) M.val N) l b)
namespace Manifest
variable (M:Tulip.Male)(l D n:ℕ)(b:Bool)(Q:Finset (Stereo N))
abbrev Core (Q:Finset (Stereo N))(n:ℕ):= Q × Fin n
local notation "C"=>Core Q n
variable (z:boxSeats l D M N b Q n)
abbrev Dawn (i:Q):= (z i).choose
abbrev Night (i:Q):= (z i).choose_spec.choose
variable {l D M Q n b}
local notation "Z" => boxSeats l D M N b Q n
local notation "DAW" => Dawn M l D n b Q
local notation "NAW" => Night M l D n b Q
lemma session (z:Z)(i:Q): Limit n D (Dawn M l D n b Q z i) (Night M l D n b Q z i) (loan (berth (badge i.val) M.val N) l b):=(z i).choose_spec.choose_spec
-- two sorts. Mix reserve graph size. index into Mini tang. signs
abbrev position (l:ℕ)(b:Bool)(i:ℕ): Per N:= instant l b i
def Front(z:Z)(i:C):Mini N:=let k:= DAW z i.1 i.2; debut i.1.val (position l b k.1) (upperL k.2)
def Rear(z:Z)(i:C):Mini N:=let k:= NAW z i.1 i.2; debut i.1.val (position l (!b) k.1) (lowerL k.2)
variable (p:l+D+l+D<N.val)
lemma front_core(z:Z)(i:C): Front z i∈ Pavilion N l D b:=by refine mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,mem_image_of_mem _ (mem_range.mpr ((session z i.1).fuel i.2).1)⟩, mem_product.mpr ⟨mem_univ _,upperUp _⟩⟩
lemma rear_core(z:Z)(i:C): Rear z i∈ TerraceG N l D (!b):=by refine mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,mem_image_of_mem _ (mem_range.mpr ((session z i.1).fuel i.2).2)⟩, (scel_sign _).mpr (lowerDo _)⟩
include p
-- sign placements arbitrary phases weighted adjusting (-1)n. in Uʲ.TQ always. 
private lemma intoC (F: Q→Fin n→Flight)(q:∀ i:Q, Injective (F i))(h:∀ i j,(F i j).1 < D) (S:Bool→SpinIdx)(t:Injective S) (b:Bool): Injective (fun i:C=> debut i.1.val (position l b (F i.1 i.2).1) (S (F i.1 i.2).2)):=by
 rintro ⟨i,a⟩ ⟨j,y⟩ hx; obtain ⟨r,v⟩:= (show full i.val (position l b (F i a).1)=full j.val (position l b (F j y).1) ∧ S (F i a).2=S (F j y).2 from Prod.mk.inj hx); obtain ⟨H,k⟩:= (sale_full ..).mp r; have he:i=j:=Subtype.ext H; subst j; have ht':(F i a).1=(F i y).1:= (instant_eq (h i a) (h i y) p).mp k; rw [q i (Prod.ext ht' (t v))]
lemma Front_in(z:Z): Injective (Front z):= intoC p (DAW z) (fun i=>(session z i).fertile) (fun i j=> ((session z i).fuel j).1) upperL upperInj b
lemma Rear_in(z:Z) : Injective (Rear z):= intoC p (NAW z) (fun i=>(session z i).ferris) (fun i j=> ((session z i).fuel j).2) lowerL lowerInj (!b)
def Γ(z:Z): Ruler (Mini N) C:= grip (Front z) (fun i=> polae N (instant l b (DAW z i.1 i.2).1))
def Λ(z:Z): Ruler (Mini N) C:= grip (Rear z) (fun i=> polae N (instant l (!b) (NAW z i.1 i.2).1))
def Kappa(z:Z)(i:Q): Op (Fin n):=chirp (loan (berth (badge i.val) M.val N) l b) (DAW z i) (NAW z i)
def Prime(z:Z) : Op C:= jump (Equiv.refl Q) fun i=> (Kappa z i)⁻¹
lemma exercise (z:Z): (Γ z)ᴴ*Γ z=1:=by refine grip_clean _ _ (Front_in p z) fun i=> ?_; rw [polae_real,polae_one]
lemma exercise' (z:Z): (Λ z)ᴴ*Λ z=1:=by refine grip_clean _ _ (Rear_in p z) fun i=> ?_; rw [polae_real,polae_one]
omit p in
lemma jumpIn (z:Z): (Γ z)ᴴ*adagio (fun x=> -zen (mixL 4 M.val x)) N * Λ z *Prime z=1:=by
 let V:=fun x=> -zen (mixL 4 M.val x); let f(i:Q):= berth (badge i.val) M.val N; let O:= Equiv.refl (↑Q); let X:=Γ z; let Y:=Λ z; have hx:Xᴴ*adagio V N*Y= jump O (Kappa z):=by
    ext ⟨i,j⟩ ⟨k,w⟩; unfold X Γ Y Λ; rw [on_grip,grip_off]; rw [jump_apply, polae_real]; dsimp only [O,Equiv.refl_apply]; by_cases h:i=k; swap
    · rw [if_neg h, adagio_h, mul_zero,zero_mul]; simpa only [Front,Rear,debut,back_home] using (Subtype.val_injective.ne h)
    subst k; rw [if_pos rfl]; change _=loan (f i) l b _ _; unfold loan f; rw [berth_u]; unfold Front Rear; dsimp only; unfold V position; ring
 unfold Prime; change _*_=_; rw [hx, jump_mul,show (fun x:Q=>Kappa z x*(Kappa z (O x))⁻¹)=(fun x=>1) from funext (fun i=> by change Kappa z i*(Kappa z i)⁻¹=1; exact (live (session z i).rank).1)]; apply jump_id
omit p in
lemma prime_pay (z:Z): ‖Prime z‖ ≤ D:= jump_bound _ _ (by positivity) fun i=> (session z i).cost
local notation "W"=> Cane N
def ReadT(z:Z) : Ruler (Mini N) C := (Cane N).val*Γ z
def ReadU (z:Z): Ruler (Mini N) C:= (Cane N).val*Λ z*Prime z
lemma readIn (z:Z): (ReadT z)ᴴ*ReadT z=1:=by unfold ReadT; rw [Matrix.conjTranspose_mul,Matrix.mul_assoc, ←Matrix.mul_assoc (W).valᴴ (W).val, show (W).valᴴ * (W).val=1 from (W).property.1, Matrix.one_mul, exercise p]
lemma upSeat (z:Z): cutM (Pavilion N l D b)*ReadT z=ReadT z:=by
 unfold ReadT; rw [←Matrix.mul_assoc, ((Ballroom.timely (Whist N l D b)).within_inter Ballroom.Ruddy|>.canePos).eq, Matrix.mul_assoc]; rw [show cutM (Pavilion N l D b) * Γ z=Γ z from grip_in _ _ _ (front_core z)]
lemma dnSeat (z:Z): cutM (TerraceG N l D (!b))*ReadU z=ReadU z:=by
 unfold ReadU; rw [← Matrix.mul_assoc (cutM _),←Matrix.mul_assoc, ((Ballroom.timely (Whist N l D (!b))).within_inter Ballroom.Scer |>.canePos).eq, Matrix.mul_assoc ((Cane _).val)]; rw [show cutM (TerraceG N l D (!b)) * Λ z=Λ z from grip_in _ _ _ (rear_core z)]
omit p in
lemma booth (z:Z): FrameP Q*ReadU z=ReadU z:=by
 unfold FrameP ReadU; rw [twist_formula]; simp_rw [Matrix.mul_assoc]; rw [←Matrix.mul_assoc (star ((W).val)) ((W).val),show star (W).val*(W).val=1 from (W).property.1,Matrix.one_mul, ←Matrix.mul_assoc (cutM _),show cutM (films Q)*Λ z=Λ z from grip_in _ _ _ (fun i=>?_)]
 unfold Rear; simp [debut, films,back_home]
lemma boothLoan (z:Z) : (ReadT z)ᴴ*reedsK M N*ReadU z=1:=by
 unfold ReadT ReadU; rw [reedsK,alf, twist_formula, Matrix.conjTranspose_mul]; let V:=adagio (fun p=>-zen (mixL 4 M.val p)) N
 change ((Γ z)ᴴ*(W).valᴴ*((W).val*V*(W).valᴴ))*_=1; simp_rw [Matrix.mul_assoc]; rw [←Matrix.mul_assoc (W).valᴴ (W).val, ← Matrix.mul_assoc (W).valᴴ (W).val, show (W).valᴴ* (W).val=1 from (W).property.1, Matrix.one_mul,Matrix.one_mul, ←Matrix.mul_assoc _ _ (Prime z), ←Matrix.mul_assoc, ←Matrix.mul_assoc] -- tune
 exact jumpIn z
lemma read_pay(z:Z) : ‖ReadU z‖ ≤ D:=by
 let U:= (W).val * Λ z; have ht: Uᴴ*U=1:=by unfold U; rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,←Matrix.mul_assoc (W).valᴴ (W).val,show (W).valᴴ * (W).val=1 from (W).property.1,Matrix.one_mul, exercise' p];
 exact (Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (grip_pay _ ht)).trans (prime_pay z)) -- tune
lemma read_pay'(z:Z) : ‖ReadT z‖ ≤ 1:= grip_pay _ (readIn p z)
end Manifest
end YM.CF.Window.Largo
