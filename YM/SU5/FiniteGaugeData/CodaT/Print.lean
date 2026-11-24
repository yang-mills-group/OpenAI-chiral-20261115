import YM.SU5.FiniteGaugeData.CodaT.Lyra
import YM.SU5.FiniteGaugeData.Cuprite.Incan
import YM.CF.Buffered.Channels
/-! # Bookkeeping leaning pieces. Charged at raw input, occupancy later after assembly. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 500000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.CodaT
open Function NormedSpace Filter Finset MeasureTheory Lattice RG Wilson AnalyticBridge Metric Pressure Galope CF CF.Pastry CF.Py.Rate
open SU Fock Reduction Reduction.Jersey Reduction.Drama Reduction.Drama.Pack Reduction.Hutch Cube Lat Window Presidio Tenant Skye Scree Graph CF.Buffered Window.Brique Next.Rank Branch Nacre
open Rush Scroll Peaks Tap Tulip Fir Cascade Avenue RouteM Spindle Heat Cuprite.Spirit Fock.Brique Relief
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{X:Fields n}{P Q:Op (Single n)} {C c H t b p:ℝ} {s k j:ℕ}{V S R:Support (More n)}
/- a display. is abstract enough for shift from Eu. not closure of funded weights. -/
abbrev Tilt(n:Side):= Op (Single n)
abbrev Sourced(n:Side):= Pane n → Tilt n
-- smallness at source footprint
abbrev fieldR (S:Support (More n))(t:ℝ)(V:Pane n):Prop:=∀ e: Edge (Seat n),e.1∈S → e.1+step e.2∈ S → SU.group.chord (V e) ≤ t
-- Territory.Small approx.$S
abbrev radiusE(S:Support (More n))(d:ℕ):Prop:=∀ i∈S,∀ j∈S, separation i j ≤ d
structure Picture(P Q:Tilt n) (d:ℕ)(t b C ξ G:ℝ) where
 F:Sourced n
 S: Support (More n)
 nonemptyP:S.Nonempty
 geography: radiusE S d
 g(u:Mosquito n)(X:Pane n): F (gauge u X) = twist (tradew n u) (F X)
 cellar(X:Pane n):Cellar (modesIn n S) (F X)
 nilQ(X:Pane n): F X * F X=0
 traceF(X:Pane n): Matrix.trace (F X)=0
 metric(X:Pane n): ‖F X‖≤ b
 rough(X:Pane n): (cup Q P (F X)).re ≤ ξ+G
 soothing(X:Pane n)(g:fieldR S t X): (cup Q P (F X)).re ≤ ξ+C
/-- invol assumptions already affordable on Unit.Seams. -/
structure Fable(P Q:Tilt n):Prop where
 tender: Standing Q P
 flip(a:Axis)(z:ℤ): twist (carR a z n) (1-P)=P
 turn(a:Axis)(z:ℤ): twist (carR a z n) (1-Q)=Q
variable (O:Fable P Q)(a:Axis)(z:ℤ){G ξ α ε δ u:ℝ}{d:ℕ}
local notation "G5"=> SU.group
local notation "Gδ"=> carR a z n
local notation "M"=> twist (carR a z n)
local notation "p₀"=> Buffered.plane a z
abbrev refF(n:Side)(a:Axis)(z:ℤ)(S: Support (More n)):= S.image ((Buffered.plane a z).anon n)
local notation "Z"=> refF n a z
local notation "Fφ"=> fling a z n
private lemma hearth {X:Pane n}(h:fieldR (Z R) t X): fieldR R t (Fφ X):=by
 let N:=(p₀).anon n
 rintro ⟨x,i⟩ hx hy
 let v:= (Signed.mirror a); let b:Site (More n):=wrap _ (2 • (z • step a))
 let T:=(posDir i).rotate v
 have hb : N x∈ Z R := Finset.mem_image_of_mem N hx
 have he : N (x+step i) ∈ Z R := Finset.mem_image_of_mem N (a:=x+step i) hy
 have hw : N (x+step i)=N x+T.vec := by
    change affine v b (x+step i)=affine v b x+ ((posDir i).rotate v).vec; rw [Lattice.Step.vec_rotate, Lattice.Step.vec_pos, affine,affine,v.act_add, add_right_comm]
 rw [hw] at he
 change SU.group.chord (T.read X (N x))≤t
 cases hq:T with| mk i0 u=>
 rw [hq] at he; cases u
 · exact h (N x,i0) hb he
 change SU.group.chord (X (N x-step i0,i0))⁻¹ ≤ t
 have hx : N x-step i0 ∈ Z R := by simpa only [show (⟨i0,true⟩ : Lattice.Step)=negDir i0 from rfl, Lattice.Step.vec_neg, sub_eq_add_neg] using he
 rw [SU.group.chord_inv]; exact h (N x-step i0,i0) hx (by change N x-step i0+step i0 ∈ _; rw [sub_add_cancel]; exact hb)
private lemma patrons(v:Pane n)(g:Mosquito n): Fφ (Lattice.gauge g v)=Lattice.gauge (g ∘ (p₀).anon n) (Fφ v):= Push.Local.pull_gauge (Signed.mirror a) (wrap _ (2 • (z • step a))) v g
abbrev Tilt.traceTurn(a:Axis)(z:ℤ)(f:Sourced n): Sourced n:= fun X=> -twist (carR a z n) (star (f (fling a z n X)))
local notation "τ"=> Tilt.traceTurn a z
namespace Picture
variable (A:Picture P Q d t b C ξ G)
local notation "Λ"=> cup Q P
include O a z
lemma forge(U:Mosquito n)(V: Pane n): Tilt.traceTurn a z A.F (gauge U V)= twist (tradew n U) (τ A.F V):=by
 unfold Tilt.traceTurn; rw [patrons, A.g,←map_star, ←twin, Lifted.gaugeSquare, Fock.twin, map_neg]
lemma frolic(X:Pane n):(cup Q P (Tilt.traceTurn a z A.F X)).re=(cup Q P (A.F (fling a z n X))).re:=by rw [Tilt.traceTurn,O.tender.priceD Gδ (O.turn ..) (O.flip ..) (A.traceF _)]; rfl
def inseam : Picture P Q d t b C ξ G where
 F:=Tilt.traceTurn a z A.F
 S:=Z A.S
 nonemptyP:= A.nonemptyP.image ((p₀).anon n)
 geography i x j y:=by
   obtain ⟨i,u,rfl⟩:=mem_image.mp x; obtain ⟨j,v,rfl⟩:=mem_image.mp y; unfold Shape.anon affine; rw [separation_translate,separation_signed]; exact A.geography _ u _ v
 g:= forge O a z A
 cellar X:=by
    have h:= (A.cellar (Fφ X)|>.starP|>.twist_t Gδ (refl_modes a z A.S)); exact ⟨by rw [Tilt.traceTurn, mul_neg,h.leftP], by rw [Tilt.traceTurn,neg_mul,h.rightP]⟩ -- syntax of pipeline?
 nilQ X:= by rw [Tilt.traceTurn, neg_mul_neg,←map_mul,←star_mul,A.nilQ _ ,star_zero,map_zero]
 traceF X:=by rw [Tilt.traceTurn, Matrix.trace_neg, trace_twist, Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose,A.traceF]; simp
 metric X:=by rw [Tilt.traceTurn,norm_neg,twist_norm,norm_star]; exact A.metric _
 rough X:=(frolic O a z A X).trans_le (A.rough _)
 soothing X h:=(frolic O a z A X).trans_le (A.soothing (Fφ X) (hearth a z h))
-- weighting ONLY once. correct thermal cost.Power.
omit O a z in
abbrev bills {n:Side}(Y:Sourced n)(α:ℝ):Mark n:= fun X=> (Real.exp α:ℂ) • quant (1+Y X.1) -- annotation α real coercion ok
lemma tenderB : Buffered.reflMark a z (bills A.F α)= bills ((inseam O a z A).F) α:= by
 funext x; let X:= fling a z n x.1; let c:ℂ:= Real.exp α; change theta Gδ (c • quant (1+A.F X))= _; let B:= inseam O a z A; change _=c • quant (1+B.F x.1)
 rw [theta_smul, ← tallied _ (A.nilQ X), ← tallied _ (B.nilQ _), ← theta_exp,theta_dg,A.traceF,star_zero,zero_smul,zero_sub,show star c=c from Complex.conj_ofReal _]; change _=c • exp (dg (-_)); rw [dg_neg] -- tune
end Picture
local notation "𝜇"=> modesIn n
local notation "G_"=> Picture.bills
/- quota constructors intentionally not scalar invariant. -/
inductive Post (P Q:Tilt n)(d:ℕ)(t b C ξ G α:ℝ): ℕ→ Support (More n)→ Mark n→Prop
 | piece (A:Picture P Q d t b C ξ G): Post P Q d t b C ξ G α 1 A.S (Picture.bills A.F α)
 | unit(V:Support (More n)): Post P Q d t b C ξ G α 0 V 1
 | both {n₀ n₁:ℕ}{S T:Support (More n)}{x y:Mark n}: Post P Q d t b C ξ G α n₀ S x→ Post P Q d t b C ξ G α n₁ T y→ Disjoint S T→Post P Q d t b C ξ G α (n₀+n₁) (S∪T) (x*y)
 | expand {k:ℕ} {S T:Support (More n)}{x:Mark n}: Post P Q d t b C ξ G α k S x→ S⊆T→ Post P Q d t b C ξ G α k T x
variable {y x:Mark n}
local notation "pay"=> Post P Q d t b C ξ G α
include a z O
lemma Post.turn (h: Post P Q d t b C ξ G α j S x) : Post P Q d t b C ξ G α j (Z S) (Buffered.reflMark a z x):=by
 induction h with
 | piece A=> rw [A.tenderB O]; exact Post.piece (A.inseam O a z) -- order O a z A
 | unit=> rw [show reflMark a z (1:Mark n)=(1:Mark n) from funext (fun i=>theta_one _)]; exact Post.unit _
 | @both n m V T x y p q D e f=>
    have h:= Finset.disjoint_image (s:=V) (t:=T) (show Injective ((p₀).anon _) from (show Involutive ((p₀).anon _) from fun i=> fling_there a z i).injective)
    rw [refF,image_union,show reflMark a z (x*y)=reflMark a z x*reflMark a z y from funext (fun i=>theta_mul _ _ _)]; exact Post.both e f (h.mpr D)
 | expand x p H =>exact Post.expand H (image_subset_image p)
omit a z O
-- unintegrated quant at ANY field. budget deficit paid by actual uncovered seats at THIS support.
namespace Post
local notation "M₀"=> ((More n))
variable (v:Scree.Loom n) (X':Orbit n) {A C':ℝ} (u0:Mosquito n) {w:ℕ}
def blight(X:Orbit n)(p:ℝ)(w:ℕ)(S:Support (More n)) : ℝ:= (discE X.1 p w∩S).card
local notation "Δ" => blight X' p w
include v X' u0
lemma avail (W:CoversU X' v w p t u u0)(aw:d ≤ w)(xb:0≤b)(xt:0≤t)(hu:0≤G)(hC:0≤C)(h:Post P Q d t b C ξ G α j S x):∃ T:Sourced n, (∀ U:Pane n,Cellar (modesIn n S) (T U) ∧ ‖T U‖≤ b) ∧ (∀ X:Pane n,T (gauge u0 X)=twist (tradew n u0) (T X)) ∧ x=Picture.bills T ((j:ℝ)*α) ∧ (cup Q P (T (gauge u0 X'.1))).re ≤ j*(ξ+C)+ (Δ S)*G:=by
 let V:= gauge u0 X'.1
 induction h with
 | piece A'=>
   simp only [Nat.cast_one,one_mul]; refine ⟨A'.F,fun U=> ⟨A'.cellar U,A'.metric U⟩,A'.g u0,rfl,?_⟩
   let S:=A'.S; let K:=discE X'.1 p w∩ S; by_cases h: K.Nonempty
   · have he:= Nat.cast_le (α:=ℝ)|>.mpr (show 1≤ K.card from card_pos.mpr h); rw [Nat.cast_one] at he; refine (A'.rough V).trans (by change ξ+G ≤ ξ+C+ (K.card:ℝ)*G; nlinarith [hu]); -- tune
   have hv: fieldR S t V:=by
      let η':= coverN X'.1 p w (coreN w); let X₀:= deckY X'.1 p w; let j:=A'.nonemptyP.choose; have hh:j∈S:=A'.nonemptyP.choose_spec
      have he:j∈η':=by by_contra l; exact h ⟨j,mem_inter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,l⟩, hh⟩⟩
      obtain ⟨i,p,q⟩:= mem_biUnion.mp he; let T:=Spindle.patch (η w) i; have he: S⊆ T:= fun y v=> Avenue.extend i j y ((A'.geography j hh y v).trans aw) q -- orientation
      intro f p' q'; exact (W.beds i p).2.2.1 f (mem_filter.mpr ⟨mem_univ _, he p',he q'⟩)
   exact (A'.soothing V hv).trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hu))
 | unit S=>
   refine ⟨0,fun U=>⟨Cellar.no_room _,norm_zero.le.trans xb⟩,by simp,?_,?_⟩ -- tune
   · funext i; unfold Picture.bills; simp [quant_one]
   · rw [show (0:Sourced n) _=0 from rfl,cup_zero]; simp only [Complex.zero_re,Nat.cast_zero, zero_mul,zero_add]; exact mul_nonneg (Nat.cast_nonneg _) hu
 | @both y z S T f g v k D e h=>
   obtain ⟨A,hA,a,a',hx⟩:=e; obtain ⟨B,hB,r,s',w'⟩:=h
   have he:= modes_orth D; refine ⟨A+B, fun U=> ?_,fun X=> ?_,?_,?_⟩
   · exact ⟨((hA U).1.stock (modes_monotone subset_union_left)).add ((hB U).1.stock (modes_monotone subset_union_right)),duo_max (hA U).1 (hB U).1 he (hA U).2 (hB U).2⟩
   · rw [Pi.add_apply, Pi.add_apply,map_add,a,r]
   · rw [a',s']; funext i; simp only [Pi.mul_apply,Picture.bills,Pi.add_apply]; rw [Matrix.smul_mul,Matrix.mul_smul,← quant_mul]; let X:=i.1; rw [show (1+ A X)*(1+B X)=1+(A X + B X) from ?_,Nat.cast_add,add_mul _ _ α,Real.exp_add,Complex.ofReal_mul,smul_smul]; simp only [add_mul,mul_add,one_mul,mul_one,(hA X).1.orthProd (hB X).1 he]; abel
   · rw [Pi.add_apply]; change (Relief.cup Q P _).re ≤ _; rw [←sub_neg_eq_add (A _),(cup_sub Q P),show ∀ X:Tilt _,Relief.cup Q P (-X)=-Relief.cup Q P X from fun X=>by unfold Relief.cup; rw [mul_neg, Matrix.trace_neg], sub_neg_eq_add, Complex.add_re]; apply (add_le_add hx w').trans_eq; let U:=discE X'.1 p w; have hp:Δ (S∪T)= (Δ S)+Δ T:=by unfold blight; rw [Finset.inter_union_distrib_left, card_union_of_disjoint (Finset.disjoint_of_subset_left inter_subset_right (Finset.disjoint_of_subset_right inter_subset_right D)),Nat.cast_add]; -- tune
     rw [hp,Nat.cast_add]; ring
 | @expand i V U f p' d h=>
    obtain ⟨A,A',q,k,e⟩:=h; refine ⟨A,fun U=>⟨(A' U).1.stock (modes_monotone d), (A' U).2⟩,q,k,?_⟩; exact e.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card (Finset.inter_subset_inter_left d))) hu)) -- check
end Post
end YM.SU5.FiniteGaugeData.CodaT
