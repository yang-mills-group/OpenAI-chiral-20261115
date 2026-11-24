import YM.SU5.FiniteGaugeData.Signal.Boathouse
/-! Cluster insertions can be very large but NATIVE high-s lattice. All lift with no wrap at
these moments. We can allow orientation-translated patch. Future chooses a particular P. -/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper
namespace IgnoreFog
variable (v:Cover) (d r k:ℕ) {n:Side}
def castle := (Lattice.box r).image (· + v)
def planar (n:Side)(v: Cover)(i:ℕ) := bay (terr (More n)) (wrap (More n) v) i
local notation "A" => wrap (More n)
lemma castle_plan (n:Side): region (castle v r) n=planar n v r:=by
 ext i; unfold region planar; rw [mem_image,bay_mem]; constructor; · rintro ⟨i',u,rfl⟩; obtain ⟨j,h,rfl⟩:=mem_image.mp u; rw [map_add]; exact Work.E08.separation_box_add _ h
 intro p; let y:= i-wrap (More n) v; refine ⟨lift y+v, mem_image_of_mem _ (Work.E08.lift_mem_box p),by rw [map_add,wrap_lift]; unfold y; abel⟩
lemma room (x:Cover): x∈castle v r ↔ x-v∈Lattice.box r:=by
 constructor; · intro h; obtain ⟨x,u,rfl⟩:=mem_image.mp h; simpa using u
 intro u; exact mem_image.mpr ⟨x-v,u,sub_add_cancel ..⟩
lemma tower {a b:ℕ}(h:a ≤ b): castle v a⊆ castle v b:= image_subset_image (fun i p=> by unfold Lattice.box at *; rw [mem_Icc] at p ⊢; constructor <;> (intro j; first| (have he:=p.1 j; simp only [] at *; omega)| (have hp:=p.2 j; simp only [] at *; omega))) -- piece
lemma extent (n:Side) : Narrowed (planar n v r) (2*r):=by
 intro i; refine ⟨v i-r,fun x p=>?_⟩; rw [←castle_plan v r] at p; obtain ⟨x,h,rfl⟩:= mem_image.mp p; have g:=box_test.mp ((room v r x).1 h); have hp:=g.1 i; have ht:=g.2 i; simp only [Pi.sub_apply] at hp ht; exact ⟨x i,by omega,by omega,rfl⟩
lemma rental(n:Side): inspected (planar n v r)⊆ planar n v (r+4):=by
 intro i p; rcases mem_union.mp p with p|p; · exact Invest.rail (by omega:r≤r+4) (wrap _ _) p
 obtain ⟨k,_,p⟩:=mem_biUnion.mp p; split at p; simp_all
 next h=> obtain ⟨j,u,w⟩:= Finset.not_disjoint_iff.mp h; have he: separation j i≤ 4:=(separation_triangle j k.1 i).trans (by rw [separation_comm j k.1]; exact Nat.add_le_add (Work.E01.sep_touched _ _ w) (Work.E01.sep_touched _ _ p)); exact (bay_mem _).mpr ((separation_triangle _ j i).trans (Nat.add_le_add ((bay_mem _).1 u) he))
private lemma lower(v:Cover) : ∃ m:ℕ,∀ n:Side,m≤ n.val→lift (wrap n v)=v:=by
 let k:= univ.sup fun i=> (v i).natAbs; refine ⟨2*k+1,fun n p=>?_⟩; apply lift_eq_iff.mpr; refine ⟨rfl, fun i=>?_⟩; have h:= (Finset.le_sup (f:=fun i=> (v i).natAbs) (mem_univ i)); change _ ≤ k at h; omega

def chart : (Axis→Fin r)→ Cover:=fun z j=> v j+(k+1)*(z j).val -- Nat multiply Int? check coercion!
lemma chart_I : Injective (chart v r k):=fun x y p=>funext (fun i=> by have ht:= congrFun p i; change v i+_ = v i+_ at ht; apply Fin.ext; unfold chart at p; have he: (k+1:ℤ)*(x i).val=(k+1:ℤ)*(y i).val:=add_left_cancel ht; exact_mod_cast (mul_left_cancel₀ (show (k+1:ℤ) ≠0 by omega) he)) -- Nat cast p

def selection := univ.image (chart v r k)
def squareWidth (r k:ℕ) := 2*(k+1)*r
def boarders (n:Side):= (selection v r k).image (wrap n)
local notation "U₀"=> selection v r k
local notation "X·" i=>nodeC i
lemma book (x:Cover) (u:x∈ U₀): nodeC x ∈ castle (nodeC v) (squareWidth r k):=by
 obtain ⟨x,u,rfl⟩:= mem_image.mp u
 have he(i:Axis): 0≤ (nodeC (chart v r k x) i - nodeC v i) ∧ nodeC (chart v r k x) i-nodeC v i ≤ (squareWidth r k:ℕ) := by
    change 0≤ (2:ℕ) • (_:ℤ)+1-((2:ℕ) • v i+1) ∧ _; -- tune
    unfold squareWidth nodeC chart; have hp:(k+1)*(x i).val ≤ (k+1)*r:=Nat.mul_le_mul_left _ (x i).isLt.le; simp [two_smul]; have hx: ((k:ℤ)+1)*(x i).val ≤(k+1:ℤ)*r:= (by exact_mod_cast hp);  nlinarith [show (0:ℤ)≤(k+1:ℤ)*(x i).val by positivity]
 apply (room ..).2 (box_test.mpr ⟨?_,?_⟩) <;> (intro i; have v:= he i; simp only [Pi.sub_apply]; omega)
lemma price_l (n:Side)(x:Site n)(t:x∈ boarders v r k n): node x∈ planar n (nodeC v) (squareWidth r k):=by obtain ⟨x,h,rfl⟩:=mem_image.mp t; rw [node_of,←castle_plan]; exact mem_image_of_mem _ (book v r k x h)
lemma widely : ∀ᶠ n:Side in atTop, distinct (boarders v r k n) k ∧ Set.InjOn (wrap n) (selection v r k):=by
 have he(x y: Cover) (p:x∈ U₀)(q:y∈ U₀)(h:x≠y): ∀ᶠ n:Side in atTop,k< separation (node (wrap n x)) (node (wrap n y)) :=by
    obtain ⟨z,u,rfl⟩:=mem_image.mp p; obtain ⟨u,w,rfl⟩:=mem_image.mp q
    let x:=chart v r k z; let y:=chart v r k u; obtain ⟨i,t⟩:= Function.ne_iff.mp (show z≠u from fun p=>h (p ▸ rfl)); let Z:= nodeC x-nodeC y
    have hg:k<(Z i).natAbs:=by
       let V:ℤ:=(z i).val; let W:ℤ:=(u i).val; have hi : V≠ W:= by unfold V W; exact_mod_cast (show (z i).val ≠ (u i).val from fun x=> t (Fin.ext x)); -- newline
       rw [show Z i=(2*(k+1):ℤ)*(V-W) from ?_,Int.natAbs_mul]; swap; · simp only [Z,x,y,V,W,nodeC,chart,two_smul,Pi.sub_apply,Pi.add_apply,Pi.one_apply]; ring
       have hu:0<(V-W).natAbs:= Int.natAbs_pos.mpr (sub_ne_zero.mpr hi); apply lt_of_lt_of_le _ (Nat.le_mul_of_pos_right _ hu); rw [show (2*(k+1):ℤ).natAbs=(2*(k+1):ℕ) from ?_]; omega; norm_cast
    obtain ⟨d,h⟩:= lower Z; filter_upwards [eventually_ge_atTop (⟨d+1,by omega⟩: Side)] with n hn; change d+1≤ n.val at hn; rw [node_of,node_of,separation,←map_sub]; apply lt_of_lt_of_le _ (component_le (wrap (More n) Z) i); rw [h (More n) (by unfold More; change d≤ n.val*2; omega)]; exact hg
 have hf:∀ᶠ n:Side in atTop,∀ x∈U₀,∀ y∈U₀,x≠y→ k < separation (node (wrap n x)) (node (wrap n y)):= (Finset.eventually_all _).2 (fun x v=> (Finset.eventually_all _).2 (fun y u=> by
    by_cases h:x=y; swap; · exact (he x y v u h).mono (fun n p _=>p)
    apply Eventually.of_forall; exact fun (i:Side) (k:x≠ y)=>False.elim (k h))) -- type annotate
 filter_upwards [hf] with n t; refine ⟨fun x p y h u=>?_,?_⟩
 · obtain ⟨i,p1,rfl⟩:=mem_image.mp p; obtain ⟨j,h1,rfl⟩:=mem_image.mp h; exact t i p1 j h1 (fun v=> u (v ▸ rfl))
 intro x p y h u; by_contra! g; have he:= t x p y h g; rw [u,separation_self] at he; omega
lemma population : (selection v r k).card = r^4:=by unfold selection; rw [card_image_of_injective _ (chart_I v r k),card_univ]; simp [Axis]
end IgnoreFog
end YM.CF.Signal
