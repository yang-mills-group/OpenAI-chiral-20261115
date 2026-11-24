import YM.SU5.FiniteGaugeData.Maypole.Neville
/-! # Long gaps. Eu point operations, joins and priced measures -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 16000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz Real
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
open Poin Celeritas Land Leal Breve Poin.Gem
open Boundary Probe
namespace Folio
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Ω:H)(hp:∀ x:E4,M S x Ω=Ω)
-- chronology.Braces
variable {α:Type}(A:α→H.Op)(ν:α→ℕ)
local notation "Ι"=> Item α
local notation "Ω°"=> wordValue S Ω A ν
local notation "Φ"=> legis S A ν
local notation "δ"=> gapK S ν
local notation "η"=> timesA a
local notation "Γ"=> leanX S
-- rotation real. Evaluate through Bishop relations.H. may reuse all views later
abbrev mail{n:ℕ}(x: Points n)(W: Fin n→α)(L:List (Fin n)):= L.map (fun i=>(W i,x i))
lemma peering {n:ℕ}(x:Points n)(L:List (Fin n))(V:Fin n→α) : wordValue S Ω A ν (mail x V L)= meanE S Ω (A ∘ V) (ν ∘ V) x L:= by unfold wordValue mail legis; rw [Film_map]; rfl
lemma order_p(a:Axis){n:ℕ}(x:Points n)(V: Fin n→α)(L:List (Fin n)): ahead a (mail x V L) ↔ ProofOrder x a L:=List.pairwise_map
lemma e_pref (L:List Ι): ∃ (n:ℕ) (f:Fin n→α)(x:Points n), L = mail x f (Each n) :=by
 let f:=L.get; let V(i):= (f i).1; let z:= points (fun i=> (f i).2); refine ⟨L.length,V,z,?_⟩; -- get map
 refine Eq.trans (List.ofFn_get L).symm ?_; rw [mail,Each,List.ofFn_eq_map]; rfl -- tune
section
variable (p:SO)(G:Canopy H α)(S:OS.Semigroup H timeAxis)(V:Bench S)(β:G.Tile S V)
local notation "T"=>timeAxis
local notation "Ψ"=> Item G.Chip
abbrev cir(x: Item G.Chip): Item G.Chip := (G.βE p x.1, Mink.General.walk p.val x.2)
abbrev Marked(G:Canopy H α)(p:SO)(x:List (Item G.Chip)) : List (Item G.Chip):= x.map (cir p G)
local notation "A₀"=> G.dep
local notation "W'"=> wordValue S V.val G.dep G.grade
include β
lemma Steno(L:List (Item G.Chip))(F:ahead T L)(e:ahead T (Marked G p L)): wordValue S V.val G.dep G.grade L= W' (Marked G p L):=by
 obtain ⟨n,f,x,rfl⟩:=e_pref L; have hu:Marked G p (mail x f (Each n)) = mail (turnO p.val x) (G.stampE p f) (Each n):=by unfold Marked mail; rw [List.map_map]; rfl
 rw [hu] at e ⊢; rw [peering,peering]; exact β.turn n p x f _ _ (.refl _) (.refl _) ((order_p ..).1 F) ((order_p ..).1 e)
omit β
variable (t s u:ℝ)(e:Mink.Ray)(x:E4)
open Flute Haven
lemma spins : Continuous (moveB e):=Continuous.subtype_mk (show Continuous (toll e) from Units.continuous_iff.mpr ⟨show Continuous (circleB e) from (by unfold circleB; fun_prop),show Continuous (fun r:ℝ=> circleB e (-r)) from (by unfold circleB; fun_prop)⟩) _
abbrev εB(t:ℝ):= - Real.arctan t
def hourE := moveB e (εB t)
local notation "R"=> hourE t e
local notation "P" f:max=> Mink.General.walk (hourE t e).val f
local notation "γ"=> Real.cos (εB t)
lemma scalesQ: (P x) T= Real.cos (εB t)*(x timeAxis)+ Real.cos (εB t)*t*(e.along x):=by
 have he:= ttake x e (εB t) -- arg order? x y E4 in Are declarations? f
 change time (circleB e (εB t) x)= _; have hp:Real.sin (εB t)= -γ*t:=by simp only [εB,Real.sin_neg,Real.cos_neg,Real.sin_arctan,Real.cos_arctan]; ring
 rw [he,hp]; change _= _*time x+_; ring
lemma pert: |e.along x|≤ ‖SEP T x‖:=by
 have he:(e.along x)=inner ℝ (SEP T x) (magnet e):=by rw [innerSpace]; unfold Ray.along; congr 1; change _= spatial (x-x timeAxis • basis timeAxis); simp [sub_eq_add_neg] -- tune
 rw [he]; exact (abs_real_inner_le_norm ..).trans_eq (by rw [Flute.bearing,mul_one])
lemma warm_cos:0< Real.cos (εB t):=by rw [εB,Real.cos_neg]; exact Real.cos_arctan_pos t
lemma planar(z:E4)(u: 2*‖SEP T z‖< z T)(p:|t|≤1) : 0<(P z) T:=by
 rw [scalesQ]; let a:=e.along z; have hv: |t*a|≤ ‖SEP T z‖:= by rw [abs_mul]; simpa only [one_mul] using (mul_le_mul p (pert e z) (abs_nonneg _) zero_le_one)
 have hx:z T+t*a>0:=by linarith only [(abs_le.mp hv).1, norm_nonneg (SEP T z),u]
 rw [mul_assoc,←mul_add]; exact mul_pos (warm_cos t) hx
lemma distinctF{L:List (Item G.Chip)}(v:deep T L)(p:|t|≤1): ahead T (Marked G R L):=by
 refine List.pairwise_map.mpr (v.imp (fun {x y}(h:2*‖_‖< timesA T y-timesA T x)=>?_)); have he:0<(P (y.2-x.2)) T:= planar t e _ h p; rw [map_sub,PiLp.sub_apply] at he; exact sub_pos.mp he -- tune binder _ stuck
lemma posit{L:List (Item G.Chip)}(v:goodF T L)(p:|t|≤1): LaneE T 0 (Marked G R L) :=by
 refine ⟨distinctF G t e v.1 p,fun x h=>?_⟩; obtain ⟨x,w,rfl⟩:= List.mem_map.mp h; exact planar t e x.2 (v.2 x w) p
lemma negateT{L:List (Item G.Chip)}(v:goodB T L)(p:|t|≤1): BackE T 0 (Marked G R L) :=by
 refine ⟨distinctF G t e v.1 p,fun x h=>?_⟩; obtain ⟨x,w,rfl⟩:= List.mem_map.mp h; have he:= planar t e (-x.2) (by rw [map_neg,norm_neg,PiLp.neg_apply]; exact v.2 x w) p; rw [map_neg,PiLp.neg_apply] at he; exact neg_pos.mp he
end
end Folio
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
