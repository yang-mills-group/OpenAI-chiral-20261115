import YM.SU5.Selected.Cor.Light
import YM.CF.Hive.Beam
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
namespace Silks
local notation "ⅈ"=> Complex.I
variable {N:Side}{b:ℕ}
local notation "GV" f:max => tradew N f
local notation "pn" => (More N)
lemma brandW (g h: SU.E): ‖brand (g*h)-1‖ ≤ ‖brand g-1‖ +‖brand h-1‖:= by
 rw [brand_mul,show _-1= brand g*(brand h-1)+(brand g-1) from ?_]; refine (norm_add_le ..).trans ?_; rw [brand_lef,add_comm]
 rw [mul_sub,mul_one]; abel
lemma costsWalk {p:ℝ}{D:Finset (Seat N)} (U:Pane N)(t:Rightful D U 1 p)(L:Lattice.Walk)(i:Seat N)(u:∀ z∈ visits i L,z∈ D):‖brand (travel U i L)-1‖ ≤ L.length*p := by
 induction L generalizing i with
 | nil=>rw [travel,brand_one]; simp
 | cons a L ih =>
    have he : i∈D:=u i List.mem_cons_self; have hx:i+a.vec∈D:=by apply u; cases L <;> simp [visits]
    have ht{x: Edge (Seat N)}(e:x∈ leaks D) : ‖brand (U x)-1‖ ≤ p:= by rw [← brand_one]; exact (riotPort D U 1).1 t _ e
    have hl:‖brand (a.read U i)-1‖ ≤ p:=by
        obtain ⟨j,b|b⟩:=a
        · exact ht (x:=(i,j)) (mem_filter.mpr ⟨mem_univ _,he,hx⟩)
        change ‖brand (U (i-step j,j))⁻¹-1‖≤ _; rw [brand_inv,← star_one (R:=Twig),←star_sub,norm_star]; refine ht ?_; exact mem_filter.mpr ⟨mem_univ _,by simpa [sub_eq_add_neg,Step.vec] using hx,(show i-step j+step j∈D from by rwa [sub_add_cancel])⟩
    rw [travel]; apply (brandW ..).trans; refine (add_le_add hl (ih _ (fun a p=>u a (List.mem_cons_of_mem _ p)))).trans_eq ?_; rw [List.length_cons]; push_cast; ring
-- nearflat rectangle ancestry. operator estimate *on full stamped sites*. output root lives in rectangle on Cover, cost local.
lemma stampsL {o d x y:Cover} (b:ℕ)(u:d ∈ Finset.Icc x y)(Z:Finset.Icc x y ⊆ plant b o) (h:4*b < (More N).val)
    {s:ℝ}{P:Pane N}(v:Rightful (park N (plant b o)) P 1 s)(g:0≤ s) (z:Seat N) (w:z∈ park N (Finset.Icc x y)) : ‖brand (stampG (wrap pn d) P z)-1‖ ≤ (8:ℝ)*b*s:= by
 obtain ⟨z,w₀,rfl⟩:= mem_image.mp w; have ht := walk_park b d z o x y Z u w₀ h; apply (costsWalk P v _ (wrap pn d) (fun a j=> image_subset_image Z (ht a j))).trans; refine mul_le_mul_of_nonneg_right ?_ g; have he:= march_budget (N:=N) b d z o (Z u) (Z w₀); exact_mod_cast (show _ ≤ 8*b from le_trans he (by omega))
lemma stamps_loc {o d x y:Cover} (b:ℕ)(u:d ∈ Finset.Icc x y)(Z:Finset.Icc x y ⊆ plant b o)(h:4*b < (More N).val)
    {U V: Pane N}(k:Agrees (park N (Finset.Icc x y)) U V)(i:Seat N)(v:i ∈ park N (Finset.Icc x y)) : stampG (wrap pn d) U i= stampG (wrap pn d) V i:= by
 obtain ⟨z,w,rfl⟩:= mem_image.mp v; exact travel_local _ _ _ _ (fun i v₀ v₁=> k i (walk_park b d z o x y Z u w h _ v₀) (walk_park b d z o x y Z u w h _ v₁))
lemma stamps_one (p j:Seat N): stampG p (1:Pane N) j=1:=by
 unfold stampG; generalize march p j 1 = L; clear j; induction L generalizing p with
 | nil=>rfl
 | cons a b ih=> rw [travel]; unfold Step.read; cases w:a.neg <;> simp [ih]
lemma trade_invL (g:Seat N→SU.E): GV (g⁻¹)=(GV g)⁻¹:= by
 symm; apply inv_eq_of_mul_eq_one_right; rw [Hive.trade_c, mul_inv_cancel, Hive.trade_p]
lemma chartg {d:Seat N}{p:Pane N}(g:Seat N→SU.E):
     ( (GV g)* (GV (stampG d p))⁻¹ ) = (GV (stampG d (gauge g p)))⁻¹* (GV (fun _=>g d)):= by
 rw [←trade_invL,Hive.trade_c, ←trade_invL,Hive.trade_c]; apply congrArg (tradew N); funext i; change g i*(travel p _ _)⁻¹ = (_:SU.E)⁻¹*g d; unfold stampG; rw [travel_gauge,Cube.arrive]; group
private lemma brand_n (g:SU.E): ‖(matter g).val-1‖ ≤ ‖brand g-1‖ := le_max_left (‖(matter g).val-1‖) _
lemma brand_star (g:SU.E): ‖brand g⁻¹-1‖ =‖brand g-1‖:=by rw [brand_inv,←star_one (R:=Twig),←star_sub,norm_star,star_one]
-- full operator scale localized. compare to horizontal as needed.
lemma condense {S:Finset (Seat N)}{g: Seat N→SU.E}{p:ℝ}(hp:0≤p)(u:∀ x∈S, ‖brand (g x)-1‖ ≤p): ‖((GV g).val: Op (Single N))* Vo S-Vo S‖≤ p:=by
 let T:(Site N×SpinIdx) → Op SU.Slot:=fun i=> if node i.1∈ S then 1 else 0
 let F:(Site N×SpinIdx) → Op SU.Slot:=fun i=> if node i.1∈ S then ((matter (g (node i.1))).val-1:Op SU.Slot) else 0
 let Y (g:Site N×SpinIdx→Op SU.Slot): Op (Single N):= jump (Equiv.refl _) g
 have ht: Vo S=Y T:=by
    ext ⟨⟨i,b⟩,z⟩ ⟨⟨j,v⟩,t⟩; by_cases p:(i,b)=(j,v); · obtain ⟨rfl,rfl⟩:= Prod.mk.inj p; by_cases f:node i∈S <;> by_cases h:z=t <;> simp [Y,T, Vo,cutM,jump_apply, f,h]
    simp [Y,T,Vo,cutM,jump_apply,p] -- tune
 -- arithmetic
 rw [ht,show _*Y T-Y T=Y F from ?_]; apply jump_bound _ _ hp; intro i; unfold F; split_ifs with h; exact (brand_n _).trans (u _ h); simpa
 change jump _ _ * Y _ -_ = _; unfold Y; rw [jump_mul,Equiv.refl_trans,← jump_sub]; refine congrArg (jump _) (funext fun i=> ?_); rw [Pi.sub_apply]; unfold F T; simp only [Equiv.refl_apply]; split_ifs <;> simp

section shift
variable {p:ℝ}(S:Finset (Seat N)) (d: Seat N) {T:Type*}[Fintype T][DecidableEq T] (g:Seat N→SU.E)(A:WRect (Single N) T)
abbrev dressedK (U:Pane N) : WRect (Single N) T:= (tradew N ((stampG d U)⁻¹)).val* A -- WARNING parentheses inverse ambiguity intentional prefer tradew⁻¹
#print dressedK
-- fix signature def parentheses
lemma toll_1 (U:Pane N): ‖dressedK d A U‖=‖A‖:= rent_v ..
lemma bareL : dressedK d A 1=A:=by unfold dressedK; rw [show stampG d (1:Pane N)=1 from funext (fun i=> stamps_one ..), inv_one,Hive.trade_p]; exact Matrix.one_mul ..
-- $wagle$ slides after gauge fix & basis. exact $T$: arm g root. want later estimating Mark; solves by direct:
-- D(g·p) * arm(g root) = tradew(g) * D(p)
lemma pennant (x:Pane N)(b:UNI T)(p: (tradew N (fun _ => g d)).val * A= A*b.val) : dressedK d A (gauge g x)*b.val= (GV g).val*dressedK d A x:=by
 unfold dressedK; rw [trade_invL,trade_invL, Matrix.mul_assoc,←p,← Matrix.mul_assoc,←Matrix.mul_assoc (tradew N g).val]; change ((_:UNI (Single N))*_).val * A= _ -- tune
 exact congrArg (fun Z: UNI _ => Z.val*A) (chartg g).symm
lemma holdsK (S:Finset (Seat N))(x:Pane N)(u:Contained (modesIn N S) A):Contained (modesIn N S) (dressedK d A x):= sparkleT u (gauge_frost S (stampG d x)⁻¹)
lemma holdsT (b:Bool)(x: Pane N)(u: hand b (cutM (Tset N))* A=A): hand b (cutM (Tset N))* dressedK d A x=dressedK d A x:= by
 apply parlance (hand b (cutM (Tset N))) _ (tradew N (stampG d x)⁻¹) _ u; rw [handAgainst,gauge_frostT]
lemma holds_label {c:Window.Family}(x: Pane N)(u:Contained (labelQ N c) A): Contained (labelQ N c) (dressedK d A x):=by
 apply (containedT ..).mpr; intro k; unfold dressedK; rw [line_a]; exact (book_rest ..).mpr ((containedT ..).mp u k)
lemma parks_at {x y : Pane N}(u:∀ i∈S, stampG d x i= stampG d y i)(z:Contained (modesIn N S) A): dressedK d A x= dressedK d A y:=by
 apply col_own; intro i; unfold dressedK; rw [line_a,line_a]; symm; apply agreePick S ((stampG d x)⁻¹) _ _ ((containedT ..).mp z i); exact fun i h=> congrArg Inv.inv (u i h)
@[fun_prop] lemma dressed_c: Continuous (dressedK d A):= ((trade_cont N).comp ((stampG_cont d).inv)).matrix_mul continuous_const -- potential instance inv
lemma tally (d:Seat N) (U:Pane N)(z:Contained (modesIn N S) A)(p':0≤ p) (g:∀ i∈ S, ‖brand (stampG d U i)-1‖ ≤ p) : ‖dressedK d A U - A‖≤ p*‖A‖:=by
 let Z:= (stampG d U)⁻¹; rw [show dressedK d A U - A=((tradew N Z).val*Vo S-Vo S)*A from (by rw [Matrix.sub_mul,Matrix.mul_assoc, show Vo S*A=A from z])]; exact charge_mul (condense p' (fun i p=> (brand_star ..).trans_le (g i p))) le_rfl
end shift
end Silks
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Silks
#print axioms holds_label
#print axioms pennant
#print axioms tally
#print axioms stampsL
