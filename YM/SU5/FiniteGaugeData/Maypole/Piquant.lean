import YM.SU5.FiniteGaugeData.Maypole.Vagabond
/-! # Long gaps. Eu point operations, joins and priced measures -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz Complex
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
-- real shift of strip. used for density.
section
-- generic ticket, cost Time a. attach dual.Soup
variable {K:Axis→Hilbert}(W:∀ a:Axis,OS.Semigroup (K a) a)(G:Canopy (K timeAxis) α)(A':Tribe G)(b:Axis)(x:(i:Axis)→ (K i).space)(H₀:∀ p:E4,M (W b) p (x b)=x b)
local notation "Θ"=> W b
local notation "Λ"=> K b
local notation "Gv"=> Item G.Chip
abbrev receiptI (u:Axis)(w:G.Chip): (K u).Op:= useB G A' w u
local notation "A₀"=> receiptI G A' b
local notation "ι₀"=> legis Θ A₀ G.grade
local notation "X"=> x b
variable {r:Axis→ℝ≥0} (R: Cartouche G r)
local notation "d"=> (r b:ℝ)
local notation "ρ"=> R.roll b
abbrev agent (i:Fin R.count): Item G.Chip:= (R.chips i,R.points i)
abbrev ink:= (R.roll b).map (agent G R)
lemma readyFw: LaneE b (-d) (ink G b R)∧ BackE b d (ink G b R):=by
 let L:= ink G b R
 have hh:ahead b L:=List.pairwise_map.mpr (PricesRoll G r b R); have he(i)(p:i∈L): timesA b i∈ Ioo (-d) d:= by obtain ⟨z,w,rfl⟩:= List.mem_map.mp p; exact footprint G r b R z
 exact ⟨⟨hh,fun i p=>(he i p).1⟩,⟨hh,fun i p=>(he i p).2⟩⟩
local notation "I₀"=> ink G b R
local notation "N0"=> Sum.inl (α:=Bool) (β:=Fin R.count) false
local notation "N1"=> Sum.inl (α:=Bool) (β:=Fin R.count) true
local notation "µ"=> agent G R
local notation "F0" => cam W G A' b R.chips R.points
local notation "B0"=> GapK Θ (spire r b R.points) (costR G R.chips)
lemma obit (i:Fin R.count): (F0) (Sum.inr i)= stamps Θ (A₀) (µ i):=rfl
lemma Cnext(i:Fin R.count): (B0) N0 (Sum.inr i)= leanX Θ (timesA b (µ i) - -d) (0+G.grade (R.chips i)):=rfl
lemma Cspaced(i:Fin R.count): (B0) (Sum.inr i) N1=leanX Θ (d-timesA b (µ i)) (G.grade (R.chips i)+0):=rfl
lemma cargo (L:List (Fin R.count)): Film F0 B0 (L.map Sum.inr)= legis Θ A₀ G.grade (L.map µ):=by rw [Film_map,legis,Film_map]; rfl
lemma border {L:List (Fin R.count)}{i:Fin R.count}(p:R.roll b=i::L): traceB W G A' r b R= billBefore Θ G.grade (-d) 0 I₀ * legis Θ A₀ G.grade I₀ * billLast Θ G.grade d 0 I₀:=by
 let T:= R.roll b; let F:= Sum.inr (α:=Bool) (β:= Fin R.count); let V:= T.map F
 let U:=I₀; have he: (Poin.Gem.pipe G r R b)=(N0::V)++[N1] := rfl
 cases e:T.reverse with
 | nil=> have he:= List.reverse_eq_nil_iff.mp e; exact (List.cons_ne_nil i L (p ▸ he)).elim
 | cons j v=>
    have hx: T=v.reverse++[j] := by nth_rw 1 [←List.reverse_reverse T,e,List.reverse_cons]
    have hh:V=F i :: L.map F:= by unfold V T; rw [p,List.map_cons] -- indent
    have hv: V=(v.reverse.map F)++[F j]:=by unfold V; rw [hx,List.map_append,List.map_singleton];
    let B:= billBefore Θ G.grade (-d) 0 U; let C:=billLast Θ G.grade d 0 U; have hC:C=(B0) (F j) N1:=by unfold C U billLast ink; rw [show R.roll b= _ from hx,List.map_append,List.map_singleton,List.reverse_append,List.reverse_singleton]; rfl
    have hB:B=(B0) N0 (F i):=by unfold B U ink billBefore; rw [p,List.map_cons]; rfl
    change Film F0 B0 _= B * legis Θ A₀ G.grade U * C; rw [he,← show Film F0 B0 V= legis Θ A₀ G.grade U from cargo W G A' b R T,hC,hB]
    have he: Film F0 B0 (N0::V)= (B0) N0 (F i)* Film F0 B0 V:=by rw [hh,twoF,show (F0) (N0)=1 from rfl,one_mul]
    rw [←he,hv]; change Film F0 B0 (((N0::v.reverse.map F)++[F j])++ N1 :: [])= Film F0 B0 ((N0::v.reverse.map F)++[F j])* _; rw [joiningF, solitary, show (F0) N1=1 from rfl, mul_one]
-- lemma nil & Ω
include H₀
lemma service0 (h:R.roll b=[]):traceB W G A' r b R (x b)=x b ∧ star (traceB W G A' r b R) (x b)= x b:=by
 have hc:=R.behind b; rw [h,List.map_nil,List.singleton_append] at hc; have he:= (List.pairwise_cons.mp hc).1 _ List.mem_cons_self; have t:0< d- -d:=sub_pos.mpr he; rw [traceB,Poin.Gem.pipe,h,List.map_nil,List.singleton_append,twoF,solitary]; simp only [show (F0) N1=1 from rfl, show (F0) N0=1 from rfl,one_mul,mul_one, show B0 N0 N1= leanX Θ (d- -d) 0 from rfl,warm_a Θ _ t]; exact ⟨earnO (W b) _ H₀ _ t,earnO (W b) _ H₀ _ t⟩
omit H₀ in
private lemma fixesE {α:Type}{H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Ω:H)(hp:∀ x:E4,M S x Ω=Ω)(ν:α→ℕ) (U:List (Item α)) (r:ℝ)(p:BackE a r U) : billLast S ν r 0 U Ω=Ω:= by
 cases U using List.reverseRecOn with
 | nil=>rfl
 | append_singleton U i=> rw [budgetBack]; exact earnO S Ω hp _ (sub_pos.mpr (p.2 i (by simp)))
omit H₀ in
private lemma fixL {H:Hilbert}{α:Type}{a:Axis}(S:OS.Semigroup H a)(Ω:H)(hp:∀ x:E4,M S x Ω=Ω)(ν:α→ℕ)(U:List (Item α)) (r:ℝ)(p:LaneE a r U): star (billBefore S ν r 0 U) Ω=Ω:=by
 cases U with
 | nil=> rw [billBefore,star_one]; rfl
 | cons i L=> rw [budgetFoot,warm_a]; exact earnO S Ω hp _ (sub_pos.mpr (p.2 i (by simp))); exact sub_pos.mpr (p.2 i (by simp))
lemma realPlay: traceB W G A' r b R (x b)= face Θ X A₀ G.grade (-d) I₀∧ star (traceB W G A' r b R) (x b)= role Θ X A₀ G.grade d I₀:=by
 cases e:R.roll b with
 | nil=> rw [ink,e,List.map_nil]; rw [(service0 W G A' b x H₀ R e).1,(service0 W G A' b x H₀ R e).2]; change X=((1:(K b).Op)*1) X ∧ X=star ((1:(K b).Op)*1) X; rw [one_mul,star_one]; exact ⟨rfl,rfl⟩
 | cons i L=>
    rw [border W G A' b R e]; let A:= billBefore Θ G.grade (-d) 0 I₀; let B:=billLast Θ G.grade d 0 I₀; let U:=legis Θ A₀ G.grade I₀; constructor;
    · change (A*U) (B X)=(A*U) X; rw [show B X=X from fixesE _ _ H₀ _ I₀ _ (readyFw G b R).2]
    · change star (A*U*B) X=star (U*B) X; rw [mul_assoc,star_mul]; exact congrArg (fun x:(K b).space=>star (U*B) x) (fixL Θ X H₀ _ _ _ (readyFw G b R).1)
-- orth density future, dual.E
variable (U:Set (Shrine K))(Vw: Restaure W G A' U)
abbrev John (S:OS.Semigroup H a)(Ω:H)(A:α→ H.Op)(ν:α→ℕ) : Set H:= {x|∃ v:List (Item α), LaneE a 0 v∧ x= face S Ω A ν 0 v}
abbrev Hill (S:OS.Semigroup H a)(Ω:H)(A:α→H.Op)(ν:α→ℕ) : Set H:= {x|∃ v:List (Item α), BackE a 0 v∧ x= role S Ω A ν 0 v}
-- H variable clashes.Sed. Witness ANY position s & velocity shift. Either.
omit H₀ in
lemma SEP_olo(z:Cross b)(s:ℝ): ∃ w:E4,w b= -s∧ SEP b w=z:=by
 refine ⟨z.val+ -s • basis b,?_,?_⟩; · rw [PiLp.add_apply, show z.val b=0 from z.property]; simp
 apply Subtype.ext; change z.val + _-(z.val+(-s) • basis b : E4) b • basis b=z.val; rw [PiLp.add_apply, PiLp.smul_apply,show z.val b=0 from z.property]; simp
lemma dawnActor(v:Cross b)(t:ℝ)(Y:List (Item G.Chip)) : (LaneE b t Y→ M Θ v.val (face Θ (x b) (receiptI G A' b) G.grade t Y) ∈ John Θ X A₀ G.grade) ∧ (BackE b t Y→ M Θ v.val (role Θ X A₀ G.grade t Y) ∈ Hill Θ X A₀ G.grade):=by
 obtain ⟨w,z,f⟩:= SEP_olo b v t; have h:t+w b=0:=by rw [z,add_neg_cancel]
 exact ⟨fun u=>⟨shifted w Y,h ▸ headL' w t Y u,by rw [← f,←vfront Θ X H₀ A₀ G.grade w t Y u,h]⟩,fun u=>⟨shifted w Y,h ▸ tailL' w t Y u,by rw [← f,←vlatter Θ X H₀ A₀ G.grade w t Y u,h]⟩⟩ -- pipe syntax tune
lemma clerk(g:Cross b) : M Θ g.val (traceB W G A' r b R (x b)) ∈ John Θ X A₀ G.grade ∧ M Θ g.val (star (traceB W G A' r b R) (x b)) ∈ Hill Θ X A₀ G.grade:=by rw [(realPlay W G A' b x H₀ R).1,(realPlay W G A' b x H₀ R).2]; exact ⟨(dawnActor W G A' b x H₀ g (-d) I₀).1 (readyFw G b R).1,(dawnActor W G A' b x H₀ g d I₀).2 (readyFw G b R).2⟩
omit H₀
lemma secTo {H:Hilbert}(A:Set H)(h:∀ x:H, (∀ i∈ A,inner ℂ x i=0)→ x=0): Dense (Submodule.span ℂ A:Set H):=by
 let W:= Submodule.span ℂ A; letI : CompleteSpace W.topologicalClosure:=isClosed_closure.completeSpace_coe -- tune
 have he:W.topologicalClosure=⊤:=Submodule.orthogonal_eq_bot_iff.mp (by
    apply (Submodule.eq_bot_iff _).mpr; intro v k; apply h; intro i t; exact inner_eq_zero_symm.mp (k i (Submodule.le_topologicalClosure _ (Submodule.subset_span t)))) -- tune
 exact fun x=> show x∈ W.topologicalClosure from he ▸ Submodule.mem_top
include H₀ Vw
lemma courtE (p:Seance W x U b false) : Dense (Submodule.span ℂ (John Θ X A₀ G.grade):Set Λ):=by
 refine secTo _ (fun y t=>p y fun L h z=>?_); let u:= SEP b z; let Z:= M Θ u.val; obtain ⟨f,hf⟩:= Vw.pays L h; let D(i:ℕ):= oars W G A' L.t b (f i)
 have he(C:Bag G L.t): inner ℂ y (Z (oars W G A' L.t b C X))=0:=by
    induction C with
    | nil=> change inner ℂ y (Z (0:Λ))=0; rw [map_zero,inner_zero_right]
    | cons u C ih=> change inner ℂ y (Z (u.1 • (traceB W G A' L.t b u.2 X) + oars W G A' L.t b C X))=0; rw [map_add,map_smul,inner_add_right,inner_smul_right,ih,t _ (clerk W G A' b x H₀ u.2 _).1,mul_zero,zero_add]
 change inner ℂ y (orbit_on W b z L X)= _; rw [barry]; change inner ℂ y (Z (L.f b (M Θ _ X)))=_; rw [H₀]; apply tendsto_nhds_unique ((Wot.shrew (hf b) (tendsto_const_nhds (x:=Z))).funds y X); exact tendsto_const_nhds.congr' (Eventually.of_forall fun i=>(he (f i)).symm) -- shrew inspect
lemma courtL (p:Seance W x U b true) : Dense (Submodule.span ℂ (Hill Θ X A₀ G.grade): Set Λ):=by
 refine secTo _ (fun y t=>p y fun L h z=>?_); let u:= SEP b z; let Z:= M Θ u.val; obtain ⟨f,hf⟩:= Vw.pays L h; let D(i:ℕ):= oars W G A' L.t b (f i)
 have he(C:Bag G L.t): inner ℂ y (Z (star (oars W G A' L.t b C) X))=0:=by
    induction C with
    | nil=> change inner ℂ y (Z (star (0:(K b).Op) X))=0; rw [star_zero]; change inner ℂ y (Z (0:Λ))=0; rw [map_zero,inner_zero_right]
    | cons u C ih=> rw [show oars W G A' L.t b (u::C)= u.1 • traceB W G A' L.t b u.2+oars W G A' L.t b C from rfl,star_add,star_smul]; change inner ℂ y (Z (star u.1 • (star (traceB W G A' L.t b u.2) X)+star (oars W G A' L.t b C) X))=0; rw [map_add,map_smul,inner_add_right,inner_smul_right,ih,t _ (clerk W G A' b x H₀ u.2 _).2,mul_zero,zero_add]
 change inner ℂ y (star (orbit_on W b z L) X)= _; rw [barry,coreSp,versX]; change inner ℂ y (Z (star (L.f b) (M Θ _ X)))=_; rw [H₀]; apply tendsto_nhds_unique ((Wot.shrew (Wot.starred (hf b)) (tendsto_const_nhds (x:=Z))).funds y X); exact tendsto_const_nhds.congr' (Eventually.of_forall fun i=>(he (f i)).symm) -- syntax
end
#print axioms courtL
end Folio
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
