import YM.SU5.FiniteGaugeData.Concord.Script
/-!
# Construct the multilinear assembly through the highest level of this finite presentation

Evaluation of any given segment; allowed to choose any linear retractions of the map c ↦ c1 as
anchors in the unused tail (in use can even choose actual normalized readings from limits). No
hidden uniqueness assumed about levels beyond the valuation floor.
-/
noncomputable section
namespace YM.CF.Buffered.Concord.Style
set_option autoImplicit false
open Function Filter Finset PiTensorProduct
open scoped ComplexOrder BigOperators Topology Classical TensorProduct
variable {A B:Type*} [CommRing A][Algebra ℂ A] [AddCommGroup B][Module ℂ B]
variable {b n m k:ℕ} (E : ℕ→ A →ₗ[ℂ] ℂ) (q : ∀ j,E j 1=1)

/-- multilinear on positions up to and INCLUDING level n, all later positions remain irrelevant. -/
structure Skirt (A : Type*) [CommRing A][Algebra ℂ A] (B:Type*)[AddCommGroup B][Module ℂ B](n:ℕ) where
  soc : (ℕ→A)→ B
  depends {s t} : (∀ i ≤ n,s i=t i) → soc s=soc t
  add (f:ℕ→A) i (_ : i≤n) x y : soc (update f i (x+y))=soc (update f i x)+soc (update f i y)
  smul (f:ℕ→A) i (_ : i≤n) x (c:ℂ) : soc (update f i (c•x))=c • soc (update f i x)
namespace Skirt
variable (P : Skirt A B n)(f : ℕ→A)
private abbrev cost (u:ℕ) (f:ℕ→A) : ℂ := ∏ i∈ Ioc n u, E i (f i)
private def more (u:ℕ):B:= cost (n:=n) E u f • P.soc f
private def value : B := if h:passing f then P.more E f h.choose else 0
include q
private lemma priced {u v:ℕ} (h:u ≤ v)(t:fits u f) : P.more E f v=P.more E f u:=by
  unfold more cost; apply congrArg (fun c:ℂ=>c • (P.soc f)); symm; refine prod_subset (fun i h'=>mem_Ioc.mpr ⟨(mem_Ioc.mp h').1,(mem_Ioc.mp h').2.trans h⟩) ?_; intro i v b; exact (congrArg (E i) (t i (lt_of_not_ge fun p=> b (mem_Ioc.mpr ⟨(mem_Ioc.mp v).1,p⟩)))).trans (q i)
private lemma value_here {b:ℕ}(t:fits b f): P.value E f=P.more E f b:=by
  let p:passing f:=⟨b,t⟩; unfold value; rw [dif_pos p]; exact (P.priced E q f (u:=p.choose) (v:=max b p.choose) (le_max_right ..) p.choose_spec).symm.trans (P.priced E q f (le_max_left ..) t)
private lemma presence (i:ℕ)(x:A) (h:i≤ b) (p:fits b f): fits b (update f i x):=fun k v=> (update_of_ne (ne_of_gt (lt_of_le_of_lt h v)) ..).trans (p k v) -- omit q
private lemma outside (i:ℕ)(v:¬passing f)(x:A): P.value E (update f i x)=0:=by
  unfold value; refine dif_neg fun t=> v ?_; obtain ⟨n,h⟩:=t; let p:= presence E q (update f i x) i (f i) (le_max_left i n) (fits_later h (le_max_right ..)); rw [update_idem, update_eq_self] at p; exact ⟨_,p⟩
private lemma prefix_dep (i:ℕ)(h:i≤n)(x:A)(a:ℕ): cost (n:=n) E a (update f i x)=cost (n:=n) E a f:= prod_congr rfl fun j u=> by rw [update_of_ne (ne_of_gt (lt_of_le_of_lt h (mem_Ioc.mp u).1))]
private lemma suffix_dep (i:ℕ)(h:n < i)(x:A)(a:ℕ)(t:i≤a): P.more E (update f i x) a= (E i x) • ((∏ j∈ (Ioc n a).erase i, E j (f j)) • P.soc f):=by
  have hp:P.soc (update f i x)=P.soc f:=P.depends (fun j p=> update_of_ne (ne_of_lt (lt_of_le_of_lt p h)) _ _)
  have he: i∈ Ioc n a:=mem_Ioc.mpr ⟨h,t⟩
  unfold more cost; rw [hp,←insert_erase he,prod_insert (notMem_erase _ _),update_self, ←mul_smul]; apply congrArg (fun c:ℂ => c • P.soc f); congr 1; apply prod_congr (by rw [insert_erase he]); intro b t; rw [update_of_ne (ne_of_mem_erase t)]
def point : MultilinearMap ℂ (fun _:ℕ=>A) B := MultilinearMap.mk' (P.value E) (by
 intro m i x y
 by_cases f:passing m; swap; · simp [outside E q P m i f] -- tune
 let v:= max f.choose i; have hw:i≤v:= le_max_right ..; have he(c:A):= value_here E q P _ (presence E q m i c hw (fits_later f.choose_spec (le_max_left ..)))
 rw [he,he,he]; by_cases h:i≤n; swap
 · simp_rw [suffix_dep E q P m i (lt_of_not_ge h) _ v hw, map_add, add_smul]
 unfold more; simp_rw [prefix_dep E q m i h, P.add m i h, smul_add]) (by
 intro m i c x; by_cases f:passing m; swap; · simp [outside E q P m i f]
 let v:= max f.choose i; have hw:i≤v:= le_max_right ..; have he(x:A):= value_here E q P _ (presence E q m i x hw (fits_later f.choose_spec (le_max_left ..)))
 rw [he,he]; by_cases h:i≤n; swap
 · simp_rw [suffix_dep E q P m i (lt_of_not_ge h) _ v hw, map_smul, smul_eq_mul, mul_smul] -- remove c
 unfold more; simp_rw [prefix_dep E q m i h,P.smul m i h]; rw [smul_comm (cost E _ _) c]) -- α?

def hardcover : Surface A→ₗ[ℂ]B := PiTensorProduct.lift (point E q P)
lemma hardcover_app (t:fits n f): hardcover E q P (PiTensorProduct.tprod ℂ f)=P.soc f:=by
  rw [hardcover,lift.tprod]; change P.value E f=_; rw [P.value_here E q f t, more]; simp [cost]
end Skirt
end YM.CF.Buffered.Concord.Style
