import YM.SU5.FiniteGaugeData.Cirrus.Floraison
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](F: H.space→L[ℂ]E)(x:Bench S)(Ω:Bench S)(hΩ:∀ p:E4,M S p Ω.val=Ω.val)
variable {ι:Type}(G:Canopy H ι)(t:G.Token)(w:List G.Token)
local notation "D"=>Bench S
local notation "Mₜ"=>G.horizon S
local notation "X"=> List G.Token
local notation "P"=> usher S
-- All arbitrary progressions.
def Rite : X→Set (Bench S)
 | []=>{Ω}
 | t::w=> {x | ∃ (p:E4) (y:Bench S), y∈ Rite w ∧ x=P p (G.horizon S t y)}
-- small progression in the iterated-filter sense. Handles continuation of last coords first.
def Hut : X→Set (Bench S)→ Prop
 | [], U=> Ω∈ U
 | t::w, U=> ∀ᶠ p:E4 in 𝓝 0,Hut w ((P p ∘ Mₜ t) ⁻¹' U)
local notation "C"=> Rite S Ω G
local notation "W"=> Hut S Ω G
local notation "R"=> saucer S
lemma higher (U V:Set (Bench S))(u: U ⊆ V)(h:W w U): W w V:= by
 induction w generalizing U V with
 | nil=> exact u h
 | cons t w ih=> rw [Hut] at h ⊢; exact h.mono fun p h=> ih _ _ (preimage_mono u) h
variable (L:Boundary.Action H)(e:∀ p:E4,L.orbit.translation p=M S p)
include e
lemma tang (n:ℕ)(h:W w {u| F (hall S n u)=0}) : C w ⊆ {u| F (hall S n u)=0}:=by
 let Z(k:ℕ):=hall S k
 have hZ(k p y): Z k (P p y)=M S p (Z k y):= park_κ S k _ _ _ _ ((tread S p).symm.pow_right k)
 induction w generalizing n F with
 | nil=> rw [Rite,singleton_subset_iff]; exact h
 | cons t w ih=>
    rintro u ⟨p,y,g,rfl⟩
    change F (Z n _)=0; rw [hZ]; apply still S F (Z n (Mₜ t y)) L e 0 _ p
    let K:= G.grade t.1; let m:= n; let n':=K+(K+m); let A (p:E4):= (F.comp (M S p)).comp (brochure S (G.dep t.1) (K+m) t.2)
    have hh(p y): F (Z n (P p (G.horizon S t y)))= A p (hall S n' y):=by rw [hZ]; exact congrArg (F ∘ M S p) (graphN S _ t.2 y K m)
    rw [Hut] at h; filter_upwards [h] with p z; rw [←hZ,hh]
    apply ih (A p) n' _ g
    refine higher S Ω G w _ _ ?_ z; exact fun x h=> (hh p x).symm.trans (show F (Z n (P p (G.horizon S t x)))=0 from h)
omit e
abbrev farther (q:E4)(t:G.Token):G.Token:= (t.1, ahead q t.2)
variable (q:E4)
include hΩ
lemma passArc : Rite S Ω G w ⊆ {x|P q x∈ Rite S Ω G w} :=by
 cases w with
 | nil=> rintro x g; rw [show x=Ω from (g:x∈ ({Ω}:Set (Bench S)))]; change P q Ω=Ω; exact Subtype.ext (hΩ _)
 | cons t w=> rintro x ⟨p,y,r,rfl⟩; exact ⟨q+p,y,r, ushe ..⟩
lemma holt(U:Set (Bench S))(h: W (w.map (farther G q)) U): W w (P q ⁻¹' U):=by
 induction w generalizing U with
 | nil=> rw [List.map_nil] at h; change P q Ω∈ U; rw [show P q Ω=Ω from Subtype.ext (hΩ _)]; exact h
 | cons t w ih=>
    rw [Hut]; rw [List.map_cons,Hut] at h
    filter_upwards [h] with p r
    apply higher S Ω G w _ _ _ (ih _ r); intro x v
    have h': P q (P p (Mₜ t x))= P p (G.horizon S (farther G q t) (P q x)):=by rw [ushe,show G.horizon S (farther G q t) _= P q (G.horizon S t x) from (attends S _ _ _ _ _).symm,ushe,add_comm]
    change P q (P p (G.horizon S t x))∈ U; exact h' ▸ (v : P p (G.horizon S (farther G q t) (P q x))∈ U)
omit hΩ
lemma prior (x: Bench S)(p:x∈C w) : P q (G.horizon S t x)∈ C (t::w):= ⟨q,x,p,rfl⟩
include hΩ
lemma arrives (u: Bench S)(p:u∈C w): G.horizon S (farther G q t) u ∈ C (t::w):=by
 let v:=P (-q) u; rw [show G.horizon S (farther G q t) u=P q (G.horizon S t v) from ?_]; apply prior; exact passArc S Ω hΩ G _ (-q) p; rw [show P q (G.horizon S t v)=G.horizon S (farther G q t) (P q v) from attends S _ _ _ _ _,show P q v=u from (ushe ..).trans (add_neg_cancel q ▸ uh_zero S u)] -- fix ▸
#print axioms tang
#print axioms arrives
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
