import YM.CF.Maize.Ten
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Maize
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Gloss Floe Ave Phase.Sample Jet Pastry Drapes
variable {H e p a d r k D θ δ G c d':ℝ}{n:ℕ}
abbrev leafP(m B:Side):=costG m B ⊕ Stamp m B
def due_v(m B:Side)(i:leafP m B):= Sum.elim (tenorQ) id i
abbrev padP'(m B:Side)(i:leafP m B): Support (GridN m):= pavilion m B (due_v m B i)
noncomputable def Xmas(m B:Side)(i:leafP m B):Palot.Y (GridN m):=if h:(padP' m B i).Nonempty then ⟨_,h⟩ else ⟨{0},singleton_nonempty _⟩
abbrev chairA (m B:Side)(i:leafP m B):= chairs m B (due_v m B i)
variable {W:Scroll m B (northZ m B)}
abbrev seedCW(W:Scroll m B (northZ m B)) (F:Stamp m B→ Train m B e→Ewe m B) (i:leafP m B):= Sum.elim (fun i x=> hollow (seedQ W i (release x))) F i
abbrev κCost(W:Scroll m B (northZ m B))(w:Stamp m B→ℝ)(d:ℝ)(i:leafP m B):ℝ:=Sum.elim (dinQ W d) w i
variable {V:Stamp m B→ Train m B e→Ewe m B}{v:Stamp m B→ℝ}{b P α:ℝ}{hp:1≤ H}
variable(h:Budget B e d)(g: Construct m B H hp e θ (northZ m B) r b V v)
include g h
lemma κcs(i:leafP m B)(l:ScaleK a G W): Dedicated hp (due_v m B i) (seedCW W V i) (κCost W v d i)∧(κCost W v d i≠0 → Grove (terr _) (due_v m B i)):=by
 cases i with| inr i=> exact ⟨g.serve i,g.bought i⟩| inl i=>have ht:=χs i l h; exact ⟨curried _ ht,ht.2.2.2.2.1⟩
omit h g
lemma pad_max(i:leafP m B): padP' m B i⊆ (Xmas m B i).val:=by unfold Xmas; split; exact Subset.refl _; next h=> rw [not_nonempty_iff_eq_empty.mp h]; exact empty_subset _
include h g
lemma lot_n (l:ScaleK a G W) (i:leafP m B)(z:κCost W v d i≠0): (Xmas m B i).val=padP' m B i ∧ Grove (terr _) (padP' m B i):=by have he:Grove (terr _) _ := pad_grove (m:=m) (B:=B) ((κcs h g i l).2 z); refine ⟨?_,he⟩; unfold Xmas; split; rfl; next p=> exact False.elim (p (by generalize hx:padP' m B i=y; change Grove _ (padP' m B i) at he; rw [hx] at he; cases he<;> simp)) -- tune
lemma crew_max(i:leafP m B)(l:ScaleK a G W): Manifest (Ave.travel m B e H hp) (seedCW W V i) (2*κCost W v d i) (Xmas m B i).val (chairA m B i):=by
 obtain ⟨p,v,M,g,f,y,t,Hx,q⟩:=(κcs h g i l).1; let L:=welter m B e H hp; refine ⟨mul_nonneg (by norm_num) p,v.trans (pad_max i),fun i w=>(M i w).trans (le_mul_of_one_le_left p (by norm_num)),fun x t=>L.stair (pad_max i) (g x t), f, y, fun c d z e=>t c d (L.grows (pad_max i) z) e,fun t=>Hx (L.grows (pad_max i) t), q⟩
lemma lot_max(l:ScaleK a G W)(u:∀ i,cellHit m B r (dust W d) i ≤ c)(x:Index m): Gas.bill_X (stern ∘ Xmas m B) (κCost W v d) r x ≤ c+b:=by
 unfold Gas.bill_X; rw [sum_filter]; let L:=padP' m B; let k:= κCost W v d; have he(i:leafP m B):(if x∈ (stern ∘ Xmas m B) i then k i*rent r ((stern ∘ Xmas m B) i) else 0)=if x∈L i then rent r (L i)*k i else 0:=by
    by_cases t:k i=0; simp [t]; rw [show (stern ∘ _) i= L i from (lot_n h g l i t).1,mul_comm]
 simp_rw [show ∀ (i: leafP m B), κCost W v d i=k i from fun i=>rfl, he, Fintype.sum_sum_type]; have ht :=g.spends x; unfold cellHit spotHit at ht; rw [sum_filter] at ht; exact add_le_add (Gloss.hit_μ l h u x) ht -- check hit_μ signature
lemma rating (l:ScaleK a G W)(p:0 < r)(u:∀ i,cellHit m B (r) (dust W d) i ≤ c)(d':ℝ)(q:0<d')(ht:r=d'+2)(hx:2*(c+b) ≤ 1/8): Team (welter m B e H hp) (terr _) (Ave.travel m B e H hp) (fun i=>(Xmas m B i).val) (chairA m B) (fun i=>2*κCost W v d i) (seedCW W V) univ d':=by
 refine ⟨q,fun i _ v=>?_,fun i _=>crew_max h g i l,fun i=>?_⟩
 · have hk:= lot_n h g l i (right_ne_zero_of_mul v); rw [hk.1]; exact hk.2
 apply le_trans _ hx; apply le_trans _ (mul_le_mul_of_nonneg_left (lot_max h g l u i) (show 0≤(2:ℝ) by norm_num)); apply le_of_eq; unfold Gas.bill_X; rw [mul_sum, ht]; refine sum_congr rfl ?_; intro x y; simp only [Function.comp_apply]; unfold stern; ring
lemma supply_h(l:ScaleK a G W)(q:0<α)(u:∀ i,cellHit m B r (dust W d) i ≤ c)(d':ℝ)(p:degreePrice 0 α 1 ≤d')(ht:d'<1)(hx:r=P+2)(hb:8*(c+b) ≤ α): Ready (stern ∘ Xmas m B) 0 (Gas.moreK (fun i=> 2*κCost W v d i)) (P+1) α 1 d':=by
 refine ⟨q,zero_lt_one,p,ht,(fun i=>mul_nonneg (by norm_num) (crew_max h g i l).price), Gas.ticket (fun i u=>?_ ) (fun i=>mul_nonneg (by norm_num) (crew_max h g i l).price) ?_⟩
 · obtain ⟨a,b⟩:=lot_n h g l i (right_ne_zero_of_mul (right_ne_zero_of_mul u)); change Grove _ (Xmas m B i).val; exact a.symm ▸ b
 intro x; apply le_trans _ hb; apply le_trans _ (mul_le_mul_of_nonneg_left (lot_max h g l u x) (show 0≤ (8:ℝ) by norm_num)); apply le_of_eq; unfold Gas.bill_X; rw [mul_sum, show P+1+1=r by rw [hx]; ring]; apply sum_congr rfl; intro i _; unfold Gas.moreK; ring
variable {j:ℕ}{o:Odd L.val}{t:Pricing j L o (Thread j)}{R:Grasp t B e}(X:Pearl R)(Φ:Stamped j L o t)
include X Φ
lemma pay_tune (l:ScaleK a G W)(jA:1≤ j)(hg:R.roundZ ≤ (CSide m B).val)(p:0<e)(x:Train m B e)(q:x∈ Breath m B e): ∑ i:leafP m B, seedCW W V i x=chillT W θ x:=by
 rw [Fintype.sum_sum_type]; change (∑ i:costG m B,hollow (n:=Hearth m B) (seedQ W i (release x))) + (∑ i:Stamp m B,V i x) = _; rw [hollow_sum, ←cry_q X Φ jA hg p l (release x) (pays q), g.inventory x q]; rfl
end YM.CF.Maize
