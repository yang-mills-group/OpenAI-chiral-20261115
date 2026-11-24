import YM.CF.BPress.Wealth.Window
import YM.CF.BPress.Wealth.Festival
/-! Book single-band cancellations & heavy terms key. Interest here costed using all hit prices and I per-volume charges, not at fixed volume; `eq:B-Mcost`. Geometry of direct terms (all vertical gaps/chords) proved separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel
open scoped Topology BigOperators Classical Matrix
variable {s:Side}{b:BandWidth}{G:Gauge}(X:Bands s b) (R:PathData G) (d:Clip)(p:BudgetPoint)(β:ℝ)(M:ℕ)
abbrev Bonding (s:Side):= Face (Per s)
abbrev Root (s:Side) := Bonding s ⊕ (Signed× Bonding s)
-- not Pareto-weighted support. ALL kept in all channels
-- core support spends ≤ halo M+2. spares just amplitude cost, not enlargement price.
def heavy : Root s→ Config G s→ℝ := Sum.elim (fun i U=>hide d p β U i) (fun i U=>kept d p R β M i.1 U i.2)
def central : Root s→ Site s:= Sum.elim Prod.fst fun i=> Signed.act i.1 i.2.1
def depot : Root s→ Support s:= Sum.elim touched fun i=> photo i.1 (box M i.2.1)
def account (i:X.Index) : Root s→ Prop := Sum.elim (fun j=> touched j⊆ X.band i) (fun j=> let x:= Signed.act j.1 j.2.1; x∈X.band i ∧ ∀ i:X.Index,¬ ZoneNear X i (4*M) (x 0))
def retained (i:Root s): Prop:= ∀ j,¬ account X M j i
lemma letKeep (i:Signed×Bonding s): retained X M (.inr i) ↔ ∃ j, ZoneNear X j (4*M) (central (.inr i) 0):=by
 let x:=Signed.act i.1 i.2.1; constructor
 · intro p; by_contra h; obtain ⟨i',v|v⟩:=X.cover x; exact p i' ⟨v,fun j k=> h ⟨j,k⟩⟩; exact h ⟨i', time_zero X i' _ ((time_Zone X i' x).2 v) _⟩
 rintro ⟨j,v⟩ i' p; exact (show x∈ _ ∧ ∀ j, ¬ZoneNear X j _ _ from p).2 j v
lemma central_mem (i:Root s): central i∈depot M i∧ Grove (field 4 s) (depot M i) ∧ depot M i⊆ halo (M+2) {central i}:=by
 rcases i with i|i; obtain ⟨h,v,q⟩:= touched_limit i; refine ⟨h,v,fun j t=> halo_spec.mpr ?_⟩; obtain ⟨k,x,h⟩:=halo_spec.mp (q t); exact ⟨k,x, h.trans (by omega)⟩; have he : depot M (.inr i)=halo (M+2) {central (.inr i)}:= halo_photo ..; rw [he]; exact ⟨halo_subset _ _ (mem_singleton_self _), halo_g _ (.single _), Subset.refl _⟩
lemma deposit_band {i:X.Index}{h:Root s}(r:1≤M)(p:account X M i h): depot M h ⊆ X.band i:=by
 rcases h with x|⟨k,x⟩; exact p
 let j : Root s:= Sum.inr (k,x); let S:= depot M (s:=s) j; let c:=central (s:=s) j; change c∈ X.band i ∧ _ at p; obtain ⟨o,v,h⟩:= central_mem M j; have f(i':X.Index) : Disjoint S (X.gap i'):= by
    refine disjoint_left.mpr fun x s' t=> p.2 i' ?_; obtain ⟨i,v,h⟩:=halo_spec.mp (h s'); rw [mem_singleton.mp v] at h; refine ⟨x 0,(time_Zone ..).2 t, ((Grid.delta_at c x 0).trans h).trans ?_⟩; omega
 obtain ⟨i',e⟩:= pack_noGap X S v f; by_cases k:i=i'; rw [k]; exact e
 exact False.elim (disjoint_left.mp (X.band_disjoint k) p.1 (e o))
lemma no_repeat {i j:X.Index}{h:Root s}(r:1≤M)(p:account X M i h)(q:account X M j h) : i=j:=Classical.byContradiction fun x=> disjoint_left.mp (X.band_disjoint x) (deposit_band X M r p (central_mem ..|>.1)) (deposit_band X M r q (central_mem ..|>.1))
lemma kept_all {i:Signed×Bonding s}{j:X.Index}(p:ZoneNear X j (4*M) (central (.inr i) 0)): depot M (.inr i)⊆halo (5*M+2) (X.gap j):=by
 rw [show 5*M+2=4*M+(M+2) by omega]; exact (central_mem ..|>.2.2).trans (enclosed X j p)

def payC (d : Clip)(β C:ℝ) := β*(2*d.direct+2*d.linear)+chPrice*β*((2*C)^2/2)
variable {a C D σ Λ : ℝ}
theorem merit (h:R.Bounds d σ C Λ)(w:Checks M p d)(v:0≤β)(x:Root s): GEM (depot M x) (heavy R d p β M x) (payC d β C) ∧ ∀ U, 0≤ heavy R d p β M x U:=by
 have h₁:0 ≤ β*(2*d.direct+2*d.linear):=by positivity [d.tail_pos,d.quadratic_pos]
 have h₂:0≤chPrice* β*((2*C)^2/2):=by positivity [chPrice_pos]
 have he:0≤payC d β C:= add_nonneg h₁ h₂
 rcases x with i|⟨q,j⟩; refine ⟨⟨he,fun x=>?_, h_borel d p β i,h_local d p β i,h_conj d p β i⟩, fun x=>h_pos d p β i v x⟩; · rw [abs_of_nonneg (show 0≤heavy R d p β M (.inl i) x from h_pos d p β i v x)]; exact (h_cap d p β i v x).trans (le_add_of_nonneg_right h₂)
 refine ⟨⟨he,fun x=>?_,keep_meas R β q j h, keep_local R β q j w, keep_invariant R β q j h⟩,fun U=> kept_budget d p R β M U j v q⟩ -- tune
 rw [abs_of_nonneg (show 0≤heavy R d p β M (.inr (q,j)) x from kept_budget d p R β M x j v q)]; exact (keep_cap R β _ _ h v j).trans (le_add_of_nonneg_left h₁)

-- keep charges organized as per text. cancel all one-mark Weak pieces incl values with their own indicated supports. (empty ignored since no weak value there)
def oneWeak (i : X.Index)(P : Support s):= P.Nonempty ∧ P⊆ X.band i
def weakFar (P : Support s): Prop := ∀ i, ¬ oneWeak X i P
def bandH (i:X.Index)(U : Config G s):= ∑ x∈ univ.filter (account X M i), heavy R d p β M x U
def bandW (i:X.Index)(U : Config G s):= ∑ P∈ univ.filter (oneWeak X i), totalWeak d R p β M P U
def levy (i:X.Index)(U : Config G s):= bandH X R d p β M i U + bandW X R d p β M i U
def weakRest (P : Support s)(U:Config G s):ℝ:= if weakFar X P then totalWeak d R p β M P U else 0
lemma near_weak (r:Support s)(p:Grove (field 4 s) r)(v:weakFar X r): ∃ i, ¬ Disjoint r (X.gap i):=by
 by_contra! h; obtain ⟨i,k⟩:= pack_noGap X r p h; exact v i ⟨ Grid.inhabited_grove p,k⟩
private lemma greeter {ι J:Type*}[Fintype ι][Fintype J] (f:J→ ℝ)(p : ι→J→Prop)(t:∀ i j a,p i a→p j a→i=j) : ∑ a,f a= ∑ i,(∑ a∈univ.filter (p i),f a)+ ∑ a∈univ.filter (fun a=>∀ i, ¬p i a),f a:=by
 simp_rw [sum_filter]; rw [sum_comm, ←sum_add_distrib]; apply sum_congr rfl; intro i _; split; next h=> simp [h]
 next h=>
    obtain ⟨i',v⟩ := not_forall.mp h; simp only [add_zero]; rw [sum_eq_single i']; rw [if_pos (not_not.mp v)]; intro b _ w; exact if_neg (fun e=> w (t b i' i e (not_not.mp v))); simp

lemma balance (u:1≤M)(q:Thinner (s:=s) (totalWeak d R p β M) (fullWeak R p β M) a C)(k : Config G s)(h: R.inChannels d p β k=(∑ x:Face (Per s), hide d p β k x) + (∑ t:Signed, ∑ x:Bonding s, kept d p R β M t k x) + ∑ P,totalWeak d R p β M P k):
    R.inChannels d p β k=(∑ i, levy X R d p β M i k)+(∑ j∈univ.filter (retained X M),heavy R d p β M j k)+∑ P,weakRest X R d p β M P k:=by
 let f(j : Root s):=heavy R d p β M j k; let g(P:Support s):= totalWeak d R p β M P k; have he:= greeter f (account X M) (fun _ _ _ p q=> no_repeat X M u p q); have hv:= greeter g (oneWeak X) (fun i j a p q=> by obtain ⟨x,v⟩:= p.1; exact Classical.byContradiction fun t=> disjoint_left.mp (X.band_disjoint t) (p.2 v) (q.2 v))
 have ht : R.inChannels d p β k=(∑ j,f j)+∑ j,g j:= by rw [Fintype.sum_sum_type, Fintype.sum_prod_type (f:=fun a=> f (.inr a))]; exact h -- tune Root def rewrite
 rw [ht,he,hv]; simp_rw [levy,sum_add_distrib]; simp_rw [weakRest,←sum_filter] -- under binder simp rw
 dsimp only [retained,weakFar,bandW,bandH,g,f]; rw [show (retained X M)=fun i=>∀ j,¬account X M j i from rfl]; abel_nf; rw [show ∀ a b c d:ℝ,a+(b+(c+d))=a+(c+(b+d)) from fun a b c d=>by ring]; congr!
end YM.CF.BPress.Wealth
