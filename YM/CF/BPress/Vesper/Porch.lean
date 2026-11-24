import YM.CF.BPress.Vesper.Chorus
/- Joined covariance. Context uses A as tilted; draw always from M (un-tilted). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Palmer Fock Pastry Pine Pf Leaves EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable {B Y:Type}[Fintype B][DecidableEq B][Fintype Y][DecidableEq Y]{S:Branch.Field Y}
abbrev TripC(I:Type):= Lens I (LeanV I)
scoped instance (priority:=2000) : LE (TripC I) := (inferInstance : LinearOrder (TripC I)).toLE
scoped instance (priority:=2000) : LT (TripC I) := (inferInstance : LinearOrder (TripC I)).toLT
scoped instance (priority:=2000) : Preorder (TripC I) := (inferInstance : LinearOrder (TripC I)).toPreorder
abbrev SpinIndex := Option Bool
def flavor : TripC I→ SpinIndex:= lit (fun _=>none) (fun p=> some p.1)
def throat : TripC I→ I:= lit id Prod.snd
def park : SpinIndex→ I→TripC I| none,i=> leftS i|some b,i=>rightS (b,i)
lemma surge (i:TripC I): (∃ x:I,i=leftS x)∨ (∃ y:LeanV I,i=rightS y):= by obtain ⟨x,rfl⟩:= (toLex (α:=I⊕LeanV I)).surjective i; cases x; exact Or.inl ⟨_,rfl⟩; exact Or.inr ⟨_,rfl⟩
lemma parked (i:TripC I): park (flavor i) (throat i)=i:=by rcases surge i with ⟨j,rfl⟩|⟨j,rfl⟩ <;> rfl
lemma lip_park (x:SpinIndex)(i:I): flavor (park x i)=x ∧ throat (park x i)=i:=by cases x <;> exact ⟨rfl,rfl⟩
lemma generator (x:SpinIndex): Injective (park x (I:=I)):= Function.LeftInverse.injective (g:=throat) (fun i=>(lip_park x i).2)
def dad (C M:Op I) : SpinIndex→ Op I | none=>Lily.φ C | some true=>1-M | some false=>0
def mom (M:Op I) : SpinIndex → Op I | none=>Lily.ϕ I| some true=>0| some false=>cc M
abbrev tripP(C M:Op I) : TripC I→ Op I:=dad C M ∘ flavor
abbrev tripW(M: Op I) :TripC I→ Op I:=mom M ∘ flavor
abbrev sneak (C: Op I)(h:Cᵀ= -C) :Poly I I:= ⟨Lily.glyph C,Lily.glyph_duo h⟩
abbrev spend (C M:Op I)(i : TripC I):= introW (tripP C M i) (tripW M i) (throat i)
lemma leftW (C M: Op I)(i:I): spend C M (leftS i)=Lily.glyph C i:=rfl
lemma rightW(C M:Op I)(i:LeanV I): spend C M (rightS i)=drawT M i:=by
 rcases i with ⟨(_|_),i⟩ -- cases Bool syntax
 · change introW (0:Op I) (cc M) i=hideF M i; rw [introW,letters,l_basis]; simp [hideF,prong] -- tune hideF
 · change introW (1-M) 0 i=seekF M i; rw [introW,letters,l_basis]; simp [seekF,prong] -- tune simp priority
abbrev fair (x y:TripC I) :Prop := (ofLex x).isLeft ∨ (ofLex y).isRight
variable {C M A P Q L: Op I}{R T: Finset I}{r c:ℝ}{E: EdgeD (TripC I) B Y S}(b:B→ℂ)
variable (g:Arrange R T L A C c r)(t:IsStarProjection M){u:Wave I} (p:Top A u)
abbrev fees (P Q L A C M:Op I)(x y:SpinIndex):= contextM P Q L A C (dad C M x) (mom M x) (dad C M y) (mom M y)
abbrev Posts (x y:TripC I)(P Q L A C M:Op I):ℂ:= fees P Q L A C M (flavor x) (flavor y) (throat x) (throat y)
local notation "P_"=>cutM R
local notation "Q_"=>cutM T
local notation "𝔟"=>braC R T C
include p g
lemma lit_post(x y:TripC I): Posts x y P_ Q_ L A C M=wick 𝔟 u (spend C M x*spend C M y):=(frameC g p (tripP C M x) (tripW M x) ..).symm -- tune binder
include t
lemma post_op(x y:TripC I)(h:fair x y)(e:y≤x): Posts x y P_ Q_ L A C M+ Posts y x P_ Q_ L A C M=0:=by
 rw [lit_post g p, lit_post g p, ←wick.add]; suffices he: antiB (spend C M x) (spend C M y)=0 by rw [wick, show _+_= (0:FC I) from he,act_zero,inner_zero_right,zero_div]
 rcases surge x with ⟨i,rfl⟩|⟨i,rfl⟩ <;> rcases surge y with ⟨j,rfl⟩|⟨j,rfl⟩
 · rw [leftW,leftW]; exact Lily.glyph_duo g.bore.sk ..
 · cases e
 · rcases h with h|h<;> cases h
 rw [rightW,rightW]; exact rind M t ..
lemma fees_k {U:Type*}(f g:U→ℂ)(V: List U→ℂ)(s l:List U)(h:∀ i∈l,f i=g i) : fee f V s l=fee g V s l:=by induction l generalizing s with|nil=> rfl|cons i l ih=> rw [fee,fee,h i (List.mem_cons_self ..), ih _ (fun i t=>h _ (List.mem_cons_of_mem _ t))]
variable (q:∀ i j:TripC I, i < j→ E.bkg b i j= Posts i j (cutM R) (cutM T) L A C M)
include q
lemma post_lock (x y:TripC I)(h:fair x y): E.bkg b x y= Posts x y P_ Q_ L A C M:=by
 rcases lt_trichotomy x y with u'|v|v; · exact q _ _ u'
 all_goals have ht: E.bkg b y x= - E.bkg b x y:= Matrix.ext_iff.mpr (E.sk b) x y
 · subst y; exact (add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp ht)).trans (add_self_eq_zero.mp (post_op g t p x x h le_rfl)).symm -- tune
 rw [q y x v] at ht; rw [eq_neg_of_add_eq_zero_left (post_op g t p x y h v.le),ht,neg_neg] -- tune circular rewrite hazard
lemma well_order (l:List I)(k: List (LeanV I)) : (Sworn l k).Pairwise fair:= by
 rw [Sworn,List.pairwise_append]; refine ⟨ List.pairwise_map.mpr ?_, List.pairwise_map.mpr ?_, ?_⟩
 · induction l with| nil=> simp|cons i l ih=>exact List.pairwise_cons.mpr ⟨fun _ _=> (.inl rfl),ih⟩
 · induction k with|nil=>simp|cons i k ih=>exact List.pairwise_cons.mpr ⟨fun _ _=>(.inr rfl),ih⟩ -- tune syntax
 intro a h b v; obtain ⟨a,_,rfl⟩:=List.mem_map.mp h; exact Or.inl rfl
lemma shape_order (i:List (TripC I))(h:i.Pairwise fair): valueL 𝔟 u (tripP C M) (tripW M) throat i=shape (E.bkg b) i:=by
 apply ShapeFit.coin _ (E.sk b); refine ⟨fun i k u=>?_, baseL g p ..⟩; rw [recursion g p]; apply fees_k g t p -- tune args via include weird
 intro j v; exact (post_lock b g t p q i j ((List.pairwise_cons.mp (h.sublist u)).1 j v)).symm
lemma shape_pays : pays (E:=E) b 𝔟 u (sneak C g.bore.sk) (nursery M t):=by
 refine ⟨fun l k=>?_ ⟩; rw [←shape_order b g t p q _ (well_order b g t p q ..)]; apply congrArg; unfold strap; change _=( (Sworn _ _).map (spend C M)).prod; simp only [Sworn,List.map_append,List.map_map,Function.comp_def,List.prod_append,leftW,rightW]; rfl -- tune unfold valueL
end YM.CF.BPress.Vesper
