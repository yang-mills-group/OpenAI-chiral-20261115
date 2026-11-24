import SatinThinAgain
/-! # Transverse-axis mosaic. Adapt SatinThinRenew to generic labels, restricted axes. Controller on the projection f heights earlier than measured Mark. Geometry proof adapts Afterglow.twice. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal
attribute [local instance] opCStarAlgebra

open CF.Pannier.Chancel
variable {N B:Side}{D:ℕ}
namespace Tower.SlabMark.Cardigan
open Again (plusAgain additional plusAgain_pos)
/-! # Physical checker procedure. Only its root structure is tracked in CS!
Derived from CF.Pannier.Chancel.Cliplet.StageTw; supports even much richer v Marks under these constraints. -/
variable {M:Side}{α:Type*}(p:α→ Mark M)(F:Mark M→ℂ)
structure Grace (B:Side)(ρ:α→Seat N)(χ:Axis→ℤ→α→α)(D T:ℕ)(p:α→Mark M)(F:Mark M→ℂ)(q:ℤ→ℤ)(w:ℕ):Prop where
  nodex: ∀ i s x,ρ (χ i s x)= (plane i s).anon N (ρ x)
  free : ∀ x, AtSupport false univ (p x)
  gap:T<2*D
  price: ∀ (i:Axis)(s:ℤ)(x:α), ρ x∈ band N i s D→ AtSupport false (band M i (q s) w) (p x)
  spin: ∀ i s x,p (χ i s x)= reflMark i (q s) (p x)
  heat: ∀ i (s:ℤ)(f:Mark M), let z:= q (Heat.gaugeShift B s); AtSupport false (band M i z w) f→ ‖F f‖^2 ≤ ‖F (reflMark i z f*f)‖
-- no nonempty, for theorem
variable {T k w b:ℕ}{q:ℤ→ℤ}{d:ℝ}
variable {p F}{ρ:α→Seat N}{χ:Axis→ℤ→α→α}
     (h:Grace B ρ χ D T p F q w)
variable (l:List (α))
def spun (χ:Axis→ℤ→α→α) (a:Axis)(s:ℤ) (l:List (α)) := l.map (χ a s)
-- avoid requiring lean ρ as p.Skye nonsense
abbrev outdoor (ρ:α→Seat N) (T:ℕ)(l:List (α)):= l.Pairwise (fun x y=> T<separation (ρ x) (ρ y))
abbrev upperRoll (ρ:α→Seat N) (l:List (α)) := (l.map ρ).toFinset
include h
lemma spinning (i:Axis)(s:ℤ) : upperRoll ρ (spun χ i s l++l)= (upperRoll ρ l).image ((plane i s).anon N) ∪ upperRoll ρ l:=by
 let f: Seat N → Seat N:= (plane i s).anon N
 have u:ρ ∘ χ i s = f ∘ ρ:= funext fun j=> h.nodex ..
 unfold upperRoll spun; rw [List.map_append,List.toFinset_append,List.map_map,u,←List.map_map]; congr 1; ext x; simp [f] -- maybe orientation nodex
lemma inside_more (i:Axis)(s:ℤ)(z:T < 2*D)(u: outdoor ρ T l)(v:upperRoll ρ l⊆ band N i s D): outdoor ρ T (spun χ i s l ++l):=by
 apply List.pairwise_append.mpr; unfold spun; refine ⟨ List.pairwise_map.mpr ?_,u,?_⟩
 · refine u.imp (by intro x y f; simp only [h.nodex,Shape.anon,affine,separation_translate,separation_signed]; exact f)
 rintro _ g y w
 obtain ⟨x,t,rfl⟩:=List.mem_map.mp g; rw [h.nodex, separation_comm]; exact lt_of_lt_of_le z (opposite_gap _ _ (by omega:D>0) _ _ (v (List.mem_toFinset.mpr (List.mem_map_of_mem w))) (Finset.mem_image_of_mem _ (v (List.mem_toFinset.mpr (List.mem_map_of_mem t))))) -- syntax

lemma wear_in (i:Axis)(s:ℤ)(v:upperRoll ρ l⊆ band N i s D): AtSupport false (band M i (q s) w) (l.map p).prod:=by
 induction l with
 | nil=> exact AtSupport.oneM _
 | cons j l ih=> simp only [upperRoll,List.map_cons,List.toFinset_cons,insert_subset_iff] at v; exact (h.price i s j v.1).mulM (ih v.2) -- simp List.
lemma spun_price (i:Axis)(s:ℤ): ((spun χ i s l).map p).prod=reflMark i (q s) (l.map p).prod:=by
 induction l with
 | nil=> exact funext fun _=> (Fock.theta_one _).symm
 | cons j l ih=> rw [show spun χ i s (j::l)=χ i s j::spun χ i s l from rfl]; rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,h.spin,ih]; exact funext fun _=> (Fock.theta_mul ..).symm
lemma moreTime (i:Axis)(v: outdoor ρ T l)(e:cows i (upperRoll ρ l) b)(u: 2^k*(b+plusAgain B D)≤ N.val)(f:∀ x:Fields M, ‖(l.map p).prod x‖ ≤ d):
    ∃ y:List (α),outdoor ρ T y ∧ y.length=2^k*l.length ∧ (∀ x:Fields M, ‖(y.map p).prod x‖ ≤ d^(2^k)) ∧ ‖F (l.map p).prod‖^(2^k)≤ ‖F (y.map p).prod‖ ∧ ∀ a:Axis,a≠i→∀ z,cows a (upperRoll ρ l) z→ cows a (upperRoll ρ y) z:=by
 induction k generalizing d l b with
 | zero=> exact ⟨l,v,by simp,by simpa using f,by simp,fun _ _ _ s=>s⟩
 | succ k ih=>
    have hp:b+plusAgain B D≤ N.val:= u.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z,hz,v',g⟩:= additional i e hp
    let s:= Heat.gaugeShift B z; let Z:= q s; let W:= spun χ i s l++l; let U:Mark M:= (l.map p).prod; let K:Mark M:= (W.map p).prod
    have ht:K=reflMark i Z U*U:= by unfold K U W; rw [List.map_append,List.prod_append,spun_price h];
    have hw:‖F U‖^2≤ ‖F K‖:=by rw [ht]; exact h.heat _ _ _ (wear_in h l i s hz)
    have hb(x:Fields M): ‖K x‖≤ d^2:= by rw [ht,Pi.mul_apply]; apply le_trans (norm_mul_le ..); have he: ∀ y,‖U y‖≤ d:=f; rw [sq,reflMark,theta_fee]; exact mul_le_mul (he _) (he _) (norm_nonneg _) ((norm_nonneg _).trans (he x))
    obtain ⟨Y,V,p',hQ,vQ,l'⟩:= ih W (inside_more h l i s h.gap v hz) (b:=2*b+plusAgain B D) (by unfold W; rw [spinning h]; exact v') (by rw [pow_succ] at u; exact u.trans' (le_of_eq (by ring))) hb
    have H: W.length=2*l.length:=by unfold W spun; rw [List.length_append,List.length_map,two_mul]
    rw [pow_succ',pow_mul,pow_mul]; exact ⟨Y,V,by rw [p',H]; ring,hQ,(pow_le_pow_left₀ (by positivity) hw _).trans vQ,fun a v s' q=>l' a v s' (by unfold W; rw [spinning h]; exact g a v s' q)⟩
-- Spill all
lemma spun_all (S:Finset Axis)(v:outdoor ρ T l)(e:∀ i∈ S,cows i (upperRoll ρ l) b)(u:2^k*(b+plusAgain B D)≤ N.val)(f:∀ x:Fields M, ‖(l.map p).prod x‖ ≤ d):
    ∃ y:List (α),outdoor ρ T y ∧ y.length=(2^k)^S.card*l.length ∧ (∀ x:Fields M, ‖(y.map p).prod x‖ ≤ d^((2^k)^S.card)) ∧ ‖F (l.map p).prod‖^((2^k)^S.card)≤ ‖F (y.map p).prod‖:=by
 induction S using Finset.induction_on generalizing l d with
 | empty=> exact ⟨l,v,by simp,by simpa using f,by simp⟩
 | @insert i S w ih=>
    obtain ⟨U,a,c,hm,t,g⟩:= moreTime h l i v (e _ (mem_insert_self ..)) u f
    obtain ⟨Z,W,he,X,Y⟩:= ih U a (fun j t=> g j (fun hv=> w (hv ▸ t)) b (e j (mem_insert_of_mem t))) hm
    rw [card_insert_of_notMem w,pow_succ',pow_mul,pow_mul]; exact ⟨Z,W,by rw [he,c]; ring,X,(pow_le_pow_left₀ (by positivity) t _).trans Y⟩
omit h in
private lemma goldilock {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega

omit h in
private lemma cubeCrowd {N g x u k : ℕ}
 (hi:x ≤ 2*N) (ho:N ≤ u*x)
 (hk:2^k*g ≤ N) (hv:N ≤ 2*2^k*g)
 (hz:g ≤ 2*u) (hp:0<g):
 let j := (2^k)^3*x
 j ≤ (2*N)^4 ∧ (2*N)^4 ≤ j*(8*u)^4 := by
 intro j
 constructor
 · have he: 2^k ≤ 2*N:=by
      have h:2^k≤N:=(Nat.le_mul_of_pos_right _ hp).trans hk
      omega
   rw [show 4=3+1 from rfl,pow_succ]
   exact Nat.mul_le_mul (Nat.pow_le_pow_left he _) hi
 have ha:2*N≤(2^k)*(8*u):=calc
   _ ≤ 2*(2*(2^k)*g) := by omega
   _ ≤ 2*(2*(2^k)*(2*u)):= by gcongr
   _ = _:=by ring
 have hb: 2*N≤x*(8*u):=by nlinarith
 rw [show 4=3+1 from rfl,pow_succ]
 exact (Nat.mul_le_mul (Nat.pow_le_pow_left ha 3) hb).trans (le_of_eq (by unfold j; ring))

lemma transverse (j:Axis){u:ℕ}
  (hu:plusAgain B D ≤ N.val)(hw:plusAgain B D ≤ 2*u)
  (hou: l.length ≤ (More N).val)
  (hd: N.val ≤ u*l.length)
  (ho:outdoor ρ T l)
  (e: ∀ i,i≠j→cows i (upperRoll ρ l) 0)
  (f:∀ x:Fields M, ‖(l.map p).prod x‖ ≤ d):

 ∃ (y:List α)(a:ℕ), outdoor ρ T y ∧
   y.length=a*l.length ∧
   (∀ x:Fields M, ‖(y.map p).prod x‖ ≤ d^a) ∧
   ‖F (l.map p).prod‖^a ≤ ‖F (y.map p).prod‖ ∧
   0<a ∧ y.length ≤ (More N).val^4 ∧ (More N).val^4 ≤ y.length*(8*u)^4:=by
 obtain ⟨k,y,Y⟩:=goldilock plusAgain_pos hu
 let S:=univ.erase j
 have ht:S.card=3:= by simp [S,card_erase_of_mem,Axis]
 obtain ⟨z,i,r,g,hx⟩:=spun_all h l S (k:=k) (b:=0) ho
     (fun i t=>e _ (mem_erase.mp t).1) (by rw [zero_add]; exact y) f
 rw [ht] at r g hx
 refine ⟨z,_,i,r,g,hx,by positivity,?_⟩
 rw [r,show (More N).val=2*N.val from Nat.mul_comm ..]
 exact cubeCrowd (by rwa [show 2*N.val=(More N).val from Nat.mul_comm ..]) hd y Y hw plusAgain_pos

lemma total (l:List α):AtSupport false univ (l.map p).prod:=by
 induction l with|nil=>exact AtSupport.oneM _| cons b l ih=> exact (h.free b).mulM ih
end Tower.SlabMark.Cardigan
end YM.CF.Buffered.Afterglow
