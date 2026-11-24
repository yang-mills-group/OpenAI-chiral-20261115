import ZecaDusk
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


namespace Monument
open Poin Boundary Probe
open Cirrus Cirrus.PavilionM

-- adapt Cirrus/Saffron for use before proving Arrival on charged fields
section
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)(U V:Set E4)
local notation "D"=> G.Model S Ω
local notation "X"=> Effort S Ω G
local notation "E"=> G.lens S Ω
local notation "Kₐ"=> Hull S Ω G
open Canopy Submodule
variable (A B:Effort S Ω G)(L:DenseRange (G.lens S Ω))
local notation "T₂"=> DualR S Ω G
variable {Z W:Effort S Ω G}
include L in
lemma uniq_δ0 (t:T₂ A B)(q:T₂ A Z): Z=B:=by ext1 x; apply lensI G S Ω; apply L.eq_of_inner_right ℂ; intro y; exact (q y x).symm.trans (t y x) -- inner eq shape

#check @agenda

lemma reserve0 (v:A∈ Hull S Ω G J U): ∃ B:X, B∈ Hull S Ω G J U∧ DualR S Ω G A B:=by
 apply Algebra.adjoin_induction (s:= (G.conduct S Ω) '' (RToken G J U)) (x:=A) (p:=fun t _=>∃ B:X,_∧ T₂ t B) _ _ _ _ v
 · rintro z ⟨j,t,rfl⟩; refine ⟨G.conduct S Ω (G.reve j),seeds S Ω G J U _ ⟨t.1,?_⟩, fun x y=> agenda G S Ω j.1 j.2 x y⟩; -- membership tsupport bar
   have he: Function.support (Probe.bar j.2)=Function.support j.2 := by ext x; simp [Function.mem_support];
   have hd: tsupport (Probe.bar j.2)=tsupport j.2:= congrArg closure he; change IsCompact _∧ _; change IsCompact (tsupport (Probe.bar j.2)) ∧ tsupport (Probe.bar j.2) ⊆ U; rw [hd]; exact t.2
 · intro r; rw [Algebra.algebraMap_eq_smul_one]; refine ⟨star r • 1,(Kₐ J U).smul_mem ( (Kₐ J U).one_mem) _,Cirrus.PavilionM.cash S Ω G _ _ ?_ r⟩; intro x y; rfl
 · rintro A B p r ⟨q,k,h⟩ ⟨v,W,e⟩; exact ⟨q+v,(Kₐ J U).add_mem k W, both S Ω G _ _ h e⟩
 rintro A B p r ⟨q,k,h⟩ ⟨v,W,e⟩; exact ⟨v*q,(Kₐ J U).mul_mem W k, exhibit S Ω G _ _ h e⟩


#check @fleet
#check @Model_foot
#check @road
#check @regi
#check @lensI
end

variable {ι:Type}{H:Hilbert}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)
   (Ω:Bench S)(hΩ:∀x:E4,M S x Ω.val=Ω.val)
local notation "J"=>Grotto S G Ω.val
local notation "T"=>springs S G Ω.val
local notation "φ"=>saint S G Ω hΩ
local notation "N"=>chapel S G Ω.val
local notation "C"=>Cove S G Ω.val
local notation "L"=> (C).subtypeL
local notation "h'"=> crystalline S G Ω.val


open Cirrus Cirrus.PavilionM
local notation "Γ"=>Sachet S G
local notation "⬝"=>side S G Ω
local notation "U"=>(N).Model (T) φ
local notation "Λ"=>(N).lens (T) φ


local notation "ω"=>mastV S G Ω hΩ
local notation "op"=>mast S G Ω hΩ
local notation "door"=>Door S G Ω hΩ

def swings (p:E4)(x:(chapel S G Ω.val).Model (T) (saint S G Ω hΩ)):U:=
  ⟨usher T p x.val,Canopy.fleet (N) _ _ (safer S G Ω hΩ) _ _ x.property⟩

/-- Cyclic unbounded field words and algebra paid here *before* boosting. -/
structure Trinket:Prop where
 real:RealStamp T
 awake:‖(φ).val‖=1
 still (p:E4): M T p (φ).val=(φ).val
 anchorTransfer: Anchor S Ω.val→Anchor T (φ).val
 total:DenseRange Λ
 words:Submodule.span ℂ (range ((N).focus T φ))=⊤
 isotone (v w:Set E4) (h:v⊆w): Hull T φ N univ v≤ Hull T φ N univ w
 starNet(v:Set E4)(a:Effort T φ N)(h:a∈Hull T φ N univ v):
      ∃ b∈Hull T φ N univ v, DualR T φ N a b ∧ ∀c,DualR T φ N a c→c=b
 translated(p:E4)(x:U):M T p (Λ x)=Λ (swings S G Ω hΩ p x)
 lifts(D:Γ)(f:Test4)(p:E4)(x:U):
      swings S G Ω hΩ p (op D f x)=op D (ahead p f) (swings S G Ω hΩ p x)
 into (x:U): L (Λ x)=(door x).val
 init: door ω=Ω

 sold (D:Γ)(f:Test4)(x:U): door (op D f x)=D.val.field S f (door x)
 field (D:Γ)(f:Test4)(x:U):(op D f x).val=(⬝ D).field T f x.val
 wordEuro (α:Type)(F:α→Γ)(sp:α→Cross timeAxis)(t:α→ℝ)
    (u:List α)(e:u.Pairwise fun i j=>t i<t j):
    quoteL T (φ).val (fun x=>⬝ (F x)) sp t u=quoteL S Ω.val (fun x=>(F x).val) sp t u
 determineR (D:Γ)(A:(J).Op):
   (⬝ D).op=A ↔ ∀(f:Test4)(x:U),
   Λ (op D f x)=(ℑ T A f (D.val.n) x.val).val
 adj (D:Γ)(g:Test4)(x y:U):inner ℂ (Λ (op D g x)) (Λ y)=
    inner ℂ (Λ x) (Λ (op (twin S G D) (bar g) y))
 continuity (D:Γ)(x:U): Continuous fun f=> Λ (op D f x)
 per_net (D:Γ)(f:Test4)(e:HasCompactSupport (⇑f)): op D f∈ Hull T φ N univ (tsupport f)



local notation "amt" d:max=> posting S G Ω (Subtype.property d)

lemma boogie (D:Γ)(f:Test4)(p:E4)(x:U):
      swings S G Ω hΩ p (op D f x)=op D (ahead p f) (swings S G Ω hΩ p x):=by
 apply Subtype.ext
 change usher (T) p ((base _ _ _ (amt D) f x).val)= (base _ _ _ (amt D) (ahead p f) (swings _ _ _ hΩ p x)).val
 rw [base_money _ _ _ (amt D) f x,base_money _ _ _ (amt D) (ahead p f) _]
 exact (realStamp T).travel (post S G Ω D.property) ..

theorem trinket (e:‖Ω.val‖=1): Trinket S G Ω hΩ:=by
 have q:=safer S G Ω hΩ
 have w:=(climb_all T N φ q (pilgrims S G Ω.val))
 have d:= (N).Model_foot _ _ w
 refine ⟨realStamp _,e,q, sturdy S G Ω hΩ,d,(N).road _ _,
   fun _ _ h=>regi _ _ _ _ _ _ _ Set.Subset.rfl h,?_,
   fun _ _=>rfl,boogie S G Ω hΩ,fun _=>rfl,Subtype.ext rfl,mintedField S G Ω hΩ, ?_,
    fun _=>value2 S G Ω,fun D A=> determine T N φ (safer S G Ω hΩ)
        (posting _ _ _ D.property)
        (climb_all _ _ _ (safer S G Ω hΩ) (pilgrims S G Ω.val)) A,
    ?_,fun D=> closed_field _ _ _ (posting _ _ _ D.property),
    fun D=>gen _ _ _ (posting _ _ _ D.property)
  ⟩
 · intro v A k
   obtain ⟨B,u,t⟩:=reserve0 _ _ _ _ _ _ k
   exact ⟨B,u,t,fun _=> uniq_δ0 _ _ _ _ _ d t⟩
 · intro D f x;exact base_money _ _ _ (posting _ _ _ D.property) f x
 intro D g x w
 change inner ℂ (door (op D g x)).val (door w).val=inner ℂ
    (door x).val (door (op (twin S G D) (bar g) w)).val
 rw [mintedField,mintedField];exact (realStamp S).adj D.val g _ _

#print axioms trinket
