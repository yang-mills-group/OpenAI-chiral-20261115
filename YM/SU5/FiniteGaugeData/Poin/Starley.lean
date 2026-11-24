import YM.SU5.FiniteGaugeData.Poin.Cercle
import YM.SU5.FiniteGaugeData.Poin.Loot
import YM.Fields.System
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute MeasureTheory Boundary Probe
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "tt"=>timeAxis
variable {H:Hilbert}{α:Type}(M':Canopy H α)(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ z:E4,M S z Ω.val=Ω.val)
variable {n:ℕ} (p q:Mink.Poincare)
namespace Canopy
variable (t u:M'.Token)(chip:M'.Chip)(g:Test4)(w:List M'.Token)
local notation "D"=>Bench S
local notation "J"=> M'.Model S Ω
local notation "L"=>M'.Ticket S Ω
local notation "A"=>M'.horizon S
variable (Xw:M'.Warrant S Ω)(e:∀ b:Mink.Ray, Shelf S (magnet b))(E:M'.Climb S Ω=⊤)
def Use (p:Mink.Poincare)(X:H.Op):Prop:= ∀ w:List M'.Token,X (M'.Ticket S Ω w)=M'.Ticket S Ω (M'.moved p w)
variable (V:H.Op)
include E
lemma highRoad : Dense (Submodule.span ℂ (Set.range (M'.Ticket S Ω)):Set H):=by rw [← models]; intro x; exact show x∈Climb M' S Ω from (E ▸ Submodule.mem_top)
def Hat (E:Climb M' S Ω=⊤): Kernel.Gram (fun i j: List M'.Token=>inner ℂ (L i ) (L j)):= ⟨H,L,highRoad _ _ _ E,fun _ _=>rfl⟩
lemma arch_eq (p:H.Op)(q:H.Op)(h:∀ i:List M'.Token,p (L i)= q (L i)): p=q:= Kernel.Gram.by_bud (Hat M' S Ω E) h
include Xw hΩ e
lemma earns : ∃ Z:H.Op,M'.Use S Ω p Z∧ ‖Z‖≤1:=by
 let V(f):= L (M'.moved p f); let h:= Hat M' S Ω E; let T:= Finsupp.linearCombination ℂ V; have he(w:List M'.Token →₀ ℂ):inner ℂ (T w) (T w)=inner ℂ (h.stems w) (h.stems w):=by
    let L':= L; change inner ℂ (T w) (T w)=inner ℂ (Finsupp.linearCombination ℂ L' w) (Finsupp.linearCombination ℂ L' w); unfold T; simp only [Finsupp.linearCombination_apply,Finsupp.sum,sum_inner,inner_sum, inner_smul_left,inner_smul_right]; have ht(i j): inner ℂ (V i) (V j)=inner ℂ (L' i) (L' j):= grain M' S Ω hΩ p i Xw e j
    simp only [ht]
 suffices ht: ∀ f,‖T f‖ ≤ 1*‖h.stems f‖ from let ⟨U,b,q⟩:= Kernel.Gram.by_bound h V 1 zero_le_one ht; ⟨U,q,b⟩
 intro f; rw [one_mul,@norm_eq_sqrt_re_inner ℂ, he f,←@norm_eq_sqrt_re_inner ℂ]
omit hΩ Xw e in
private lemma muscle (V:Mink.Poincare→ H.Op)(p:∀ g,M'.Use S Ω g (V g))(q:∀ g,‖V g‖≤1)(y:H): Continuous fun g=> V g y:=by
 let T:=M'.Hat S Ω E
 have he(g:Mink.Poincare)(w): V g (M'.Ticket S Ω w)=M'.Ticket S Ω (M'.moved g w):=p g w
 let TT:= Finsupp.linearCombination ℂ (L); have hTT: DenseRange TT:= T.whole
 have hv (t: List M'.Token→₀ℂ): Continuous (fun x => (V x) (TT t)) := by
    induction t using Finsupp.induction_linear with
    | zero => simp only [map_zero]; exact continuous_const
    | add i j hi hj => simp_rw [map_add]; exact hi.add hj
    | single x k=> simp_rw [TT,Finsupp.linearCombination_single,map_smul]; change Continuous (fun t=> k • (V t (L x))); simp_rw [he]; exact continuous_const.smul (lifting ..)
 have Hk(g:Mink.Poincare)(u:H): ‖V g u‖≤‖u‖:= ((V g).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (q g))
 refine continuous_iff_continuousAt.mpr fun x=>Metric.tendsto_nhds.mpr fun ε hε=>?_
 obtain ⟨_,⟨f,rfl⟩,h⟩:= Metric.mem_closure_iff.mp (hTT y) (ε/4) (by positivity)
 have Hx(g:Mink.Poincare): dist (V g y) (V g (TT f)) < ε/4:=by rw [dist_eq_norm,←map_sub]; exact lt_of_le_of_lt (Hk ..) ((dist_eq_norm y (TT f)) ▸ h)
 filter_upwards [Metric.tendsto_nhds.mp ((hv f).tendsto x) (ε/4) (by positivity)] with z hz
 have h₁:= dist_triangle (V z y) (V z (TT f)) (V x y); have h₂:= dist_triangle (V z (TT f)) (V x (TT f)) (V x y); rw [dist_comm (V x (TT f))] at h₂; linarith [Hx z,Hx x]
-- Some parameters included.E/h.W.WH future.
theorem actionC : ∃ V: Boundary.Action H, ∀ p:Mink.Poincare, M'.Use S Ω p (V.V p):=by
 choose U ht h using fun (p:Mink.Poincare)=> M'.earns S Ω hΩ p Xw e E
 have v(p:Mink.Poincare)(w): U p (L w) = L (M'.moved p w):= ht p w
 have he: U 1=1:= arch_eq M' S Ω E _ _ fun i=>by rw [v,stayed]; rfl
 have hp(p q:Mink.Poincare): U (p*q)=U p*U q:= arch_eq M' S Ω E _ _ fun i=>by change _= U p (U q (L i)); rw [v,v,v,joins]
 refine ⟨⟨U,he,hp,?_,muscle M' S Ω E U ht h⟩,ht⟩
 let fee(p:Mink.Poincare)(u:H): ‖U p u‖≤‖u‖:= ((U p).le_opNorm u).trans (mul_le_of_le_one_left (norm_nonneg _) (h p)); intro p y; refine le_antisymm (fee p y) ?_; have hz: U p⁻¹ (U p y)=y:= DFunLike.congr_fun (show U p⁻¹*U p=1 from by rw [←hp,inv_mul_cancel,he]) y; nth_rw 1 [← hz]; exact fee p⁻¹ (U p y)
#print axioms actionC
variable (U:Boundary.Action H) (v:∀ p,M'.Use S Ω p (U.V p))
omit Xw e
include v
lemma subsidiary (x:E4) : U.orbit.translation x= M S x:= arch_eq M' S Ω E _ _ (fun i=> by
 let p:= Poincare.translation x; change U.V p (L i)= _; rw [v]; exact congrArg Subtype.val (bring M' S Ω hΩ i x).symm)
omit hΩ E v
-- implement on common invariant Model.
abbrev lens : (M'.Model S Ω)→ₗ[ℂ]H:= (Bench S).subtype.comp (M'.Model S Ω).subtype
lemma lensI : Injective (M'.lens S Ω):= fun _ _ h=> Subtype.ext (Subtype.ext h)
def focus (w:List M'.Token): (J):= ⟨M'.bud S Ω w,M'.Mmem S Ω w⟩
include v
lemma keepP(p:Mink.Poincare): Set.MapsTo (U.V p) (M'.Strand S Ω:Set H) (M'.Strand S Ω) :=by
 let Z:= M'.Strand S Ω; apply (show Z ≤ Z.comap (U.V p).toLinearMap from ?_); rw [show Z=_ from models M' S Ω]; apply Submodule.span_le.mpr; rintro _ ⟨w,rfl⟩; change U.V p (L w)∈ Submodule.span ℂ (Set.range (L)); rw [v p w]; exact Submodule.subset_span ⟨_,rfl⟩
def flick (U:H.Op)(v: Set.MapsTo U ((M'.Strand S Ω):Set H) (M'.Strand S Ω)) (x:J): J:= ⟨(v (show lens M' S Ω x∈M'.Strand S Ω from (membrane M' S Ω _ x.property))).choose,
    (v (membrane M' S Ω _ x.property)).choose_spec.1⟩ -- motive Exists? .choose not show coerc. tune
variable (x y:M'.Model S Ω)
omit v in
lemma flickR (V:H.Op)(p:Set.MapsTo V (M'.Strand S Ω:Set H) (M'.Strand S Ω)): lens M' S Ω (M'.flick S Ω V p x)= V (lens M' S Ω x):= (p (membrane M' S Ω _ x.property)).choose_spec.2
def emergeC : (J →ₗ[ℂ] J) := {
 toFun:=M'.flick S Ω (U.V p) (keepP M' S Ω U v p)
 map_add' i j:= by apply lensI M' S Ω; rw [map_add]; simp only [flickR,map_add]
 map_smul' c i:=by change _= c • _; apply lensI M' S Ω; rw [map_smul]; simp only [flickR,map_smul] }
#print axioms subsidiary
local notation "η"=> emergeC M' S Ω
local notation "♯"=> M'.lens S Ω
lemma rootR : M'.lens S Ω (emergeC M' S Ω p U v x)= U.V p ((♯) x):= flickR M' S Ω x (U.V p) (keepP M' S Ω U v p)
lemma flight : emergeC M' S Ω p U v (focus M' S Ω w)=focus M' S Ω (moved M' p w):= lensI M' S Ω ((rootR M' S Ω p U v (focus M' S Ω w)).trans (v p w)) -- order
local notation "Up"=> emergeC M' S Ω p U v
lemma idle : emergeC M' S Ω 1 U v x=x:= by apply lensI M' S Ω; rw [rootR,U.one]; rfl
lemma descendC : (η (p*q) U v) x=(η p U v) ((η q U v) x):= by apply lensI M' S Ω; rw [rootR,rootR,rootR,U.mult]; rfl
lemma Flip_inc : emergeC M' S Ω p U v (emergeC M' S Ω p⁻¹ U v x)=x := by rw [← descendC,mul_inv_cancel, idle]
omit v in
def conduct : J→ₗ[ℂ] J:= (horizon M' S t |>.comp (M'.Model S Ω).subtype).codRestrict _ fun x=> advance M' S Ω t x.val x.property
omit v in
lemma convene : conduct M' S Ω t (focus M' S Ω w)=focus M' S Ω (t::w):=Subtype.ext (Eq.symm (planeV ..))
omit v in
lemma road : Submodule.span ℂ (Set.range (focus M' S Ω))=⊤:=by
 apply eq_top_iff.mpr; rintro ⟨x,p⟩ _; refine Submodule.span_induction (x:=x) (p:=fun x h=> (⟨x,h⟩:J)∈ _) ?_ ?_ ?_ ?_ p
 · rintro _ ⟨w,rfl⟩; exact Submodule.subset_span ⟨w,rfl⟩
 · exact Submodule.zero_mem _
 · intro i j h k u v; exact Submodule.add_mem _ u v
 intro a x h v; exact Submodule.smul_mem _ _ v
lemma costume : conduct M' S Ω (travel M' p t) (Up x)=Up (conduct M' S Ω t x):= by
 let Z:=(conduct M' S Ω (travel M' p t)).comp Up; let L':= (Up).comp (conduct M' S Ω t); suffices ht: x∈LinearMap.ker (Z-L') from sub_eq_zero.mp (show Z x-L' x=0 from ht); refine (show Submodule.span ℂ (Set.range (focus M' S Ω)) ≤ _ from Submodule.span_le.mpr ?_) (by rw [road]; exact Submodule.mem_top)
 rintro z ⟨w,rfl⟩; change _ - _ =(0:J); change conduct _ _ _ _ (Up (focus ..)) - Up (conduct M' S Ω t (focus ..))=0; rw [flight,convene,convene,flight]; exact sub_self _
lemma costs : U.V p (♯ (conduct M' S Ω t x))= ♯ (conduct M' S Ω (travel M' p t) (Up x)):=by rw [costume, rootR]
-- Ensure ℂ^d multipl field op restrict
omit v
def operator (t:M'.Chip)(g:Test4):= conduct M' S Ω (t,g)
def fieldMap (t:M'.Chip): Test4→ₗ[ℂ] (J→ₗ[ℂ] J) where
 toFun g:=operator M' S Ω t g
 map_add' g h:= by ext1 x; apply Subtype.ext; exact LinearMap.congr_fun (map_add (σV S (dep M' t) _) g h) _ -- orientation helps expected reducible
 map_smul' c g:=by ext1 x; apply Subtype.ext; exact LinearMap.congr_fun (map_smul (σV S (dep M' t) _) c g) _
lemma spaces : Continuous (fun g=> ♯ (operator M' S Ω chip g x)):= singular S (M'.dep chip) x.val (M'.grade chip)
lemma agenda : inner ℂ ((♯) (operator M' S Ω chip g x)) ((♯) y) = inner ℂ ((♯) x) ((♯) (operator M' S Ω (mirrorK M' chip) (Probe.bar g) y)):= legPaid M' S (chip,g) x.val y.val
lemma oV_add (n:α)(u v:colorP (M'.P n).amount) : operator M' S Ω (⟨n,u+v⟩) g= operator M' S Ω (⟨n,u⟩) g+operator M' S Ω (⟨n,v⟩) g:= by ext1 x; apply Subtype.ext; change ℑ S (M'.flash n (u+v)) g _ x.val= _; rw [map_add,anyB]; rfl
lemma oV_smul (n:α)(u:colorP (M'.P n).amount)(c:ℂ): operator M' S Ω (⟨n,c • u⟩) g= c • operator M' S Ω (⟨n,u⟩) g:=by ext1 x; apply Subtype.ext; change ℑ S (M'.flash n (c • u)) g _ x.val= _; rw [map_smul,anyC]; rfl
include E in
lemma Model_foot : DenseRange (lens M' S Ω) := by
 have he: LinearMap.range (lens M' S Ω)=Strand M' S Ω:=by rw [lens, LinearMap.range_comp]; rw [Submodule.range_subtype]; rfl
 intro x; exact show x∈ (LinearMap.range (lens M' S Ω)).topologicalClosure from (he ▸ (show x∈ Climb M' S Ω from E ▸ Submodule.mem_top)) -- membership
#print axioms costs
#print axioms fieldMap
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
