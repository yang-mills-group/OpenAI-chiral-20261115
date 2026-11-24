import YM.SU5.FiniteGaugeData.Pannier.FeastDay
import YM.CF.Continuum.Current
/-!
# Place the Letter money of any given Species.

ORIENTATION. `birthSeat` is the birth of the object Cliplet count, a **removal**
in the initial Mark, not the "birthOp creator" of Continuum/Current! Creator's coordinate per term can
be any *other* site in the physical stencil. Never identify charge separation by spin alone.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Window (mem_Tset family)
open Py.Rate.Pannier
open Work.E08
open Lifted (nodeC node_of basisC)
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{M:Tulip.Male}{n:Side}{o:Seat n}{k d:ℕ}{r:Fin k→ Site n}
abbrev VolumeX (r:Fin k → Site n): Finset (Seat n):= univ.image (node ∘ r)
def labelQ (n: Side)(f:Window.Family): Finset (Single n):= univ.filter fun i=> family i.2=f
@[simp] lemma labelAt (f:Window.Family)(i:Single n): i∈ labelQ n f ↔ family i.2=f:= by simp [labelQ]
private lemma labelT (f:Window.Family)(V:Seat n→SU.E): twist (tradew n V) (cutM (labelQ n f))=cutM (labelQ n f):=by
 apply Mir.twist_comm; ext ⟨i,b⟩ ⟨p,a⟩; unfold cutM; simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,labelAt]; by_cases g:i=p; swap; · simp only [tradew,jump_apply,Equiv.refl_apply,if_neg g,zero_mul,mul_zero]
 subst p; simp only [tradew,jump_apply,Equiv.refl_apply,↓reduceIte]; by_cases h:family b=family a; · rw [h,mul_comm]
 rw [Window.neq_block _ h,zero_mul,mul_zero]
lemma book_rest (f:Window.Family)(V:Seat n→SU.E)(x:Ket (Single n)): withinM (labelQ n f) (acts (tradew n V).val x) ↔ withinM (labelQ n f) x:=⟨trim_return (labelT ..),trim_field (labelT ..)⟩
private lemma labelKick (p:1≤j)(f:Window.Family)(M:Tulip.Male): Commute (cutM (labelQ n f)) (spar j M (1:Pane n)):=by
 ext ⟨i,i2⟩ ⟨b,b2⟩; rw [cutM,Matrix.diagonal_mul,Matrix.mul_diagonal]; simp only [labelAt, Dial.spar,profile_trivial,funde_flat j p, Matrix.kronecker_apply]; by_cases g: i2 = b2; · rw [g,mul_comm]
 rw [Matrix.one_apply_ne g,mul_zero,zero_mul,mul_zero]
section
variable {ι:Type*}[LinearOrder ι][Fintype ι]
lemma cutLane (T S:Finset ι): Commute (cutM T) (cutM S):=by
 ext i j; rw [cutM,Matrix.diagonal_mul,cutM,Matrix.diagonal_mul]; by_cases p:i=j; · subst i; rw [Matrix.diagonal_apply_eq,Matrix.diagonal_apply_eq,mul_comm]
 rw [Matrix.diagonal_apply_ne _ p,Matrix.diagonal_apply_ne _ p]; simp
lemma within_cut (S T: Finset ι){A: Ket ι}(h:withinM T A): withinM T (acts (cutM S) A):= by unfold withinM; rw [←act_mul,(cutLane T S).eq,act_mul,h]
lemma cutShift{Q:Op ι}{S T D:Finset ι}(u:Commute (cutM S) Q)(v:IsUnit (Fock.padded T Q)){x:Ket ι}(h:withinM S x): withinM S (sparkUp Q T D x):=by
 unfold sparkUp warmth; apply within_cut; let F:=Fock.padded T Q
 have ht: Commute (cutM S) F:= (( ((cutLane ..).mul_right u).mul_right (cutLane S T)).add_right ((Commute.one_right _).sub_right (cutLane ..))) -- nz
 have hp:Commute (cutM S) F⁻¹:= by
    let C:=cutM S; change C*F⁻¹= _
    nth_rw 1 [←one_mul C,←(live (show IsUnit F from v)).2,mul_assoc _ F,←ht.eq]; rw [mul_assoc,mul_assoc,(live (show IsUnit F from v)).1,mul_one]
 unfold withinM; change acts _ (acts Q (acts F⁻¹ x)) = _; rw [←act_mul, u.eq,act_mul,←act_mul (cutM S) F⁻¹,hp.eq,act_mul,h]
end

-- Stand computed in local frames. actual removal X, transported plus Y.
abbrev Poi(x:Site n)(i:SU.Slot):Single n:=((x,(2:SpinIdx)),i)
abbrev Waved(x:Site n)(i:SU.Slot):= basisKet (Poi x i)
def chartG (N:Side)(o: Seat N)(x:Pane N):Op (Single N):=(tradew N (stampG o x)).val
lemma trade_cont (n:Side) : Continuous (fun g:Seat n→SU.E=>(tradew n g).val) :=by
 apply continuous_matrix; intro i j; unfold tradew; simp only [jump_apply]; split; exact (matter_cont.comp (show Continuous (fun g:Seat n→SU.E=> g (node i.1.1)) from continuous_apply _)).matrix_elem _ _; exact continuous_const
lemma chartG_cont : Continuous (chartG n o) := (trade_cont n).comp (stampG_cont ..)
lemma waved_const (x:Site n)(i:SU.Slot): ‖Waved x i‖=1:=by simp [Waved,basisKet]
lemma waved_pay (x:Site n)(i:SU.Slot): trim (1-cutM (Tset n)) (Waved x i):= by
 unfold trim; rw [act_sub,act_one]; suffices h:acts (cutM (Tset n)) (Waved x i)=0 by rw [h,sub_zero]
 unfold Waved Poi; rw [cut_basis]; exact if_neg (fun p=> (show ¬ (2:SpinIdx)∈plusHalf by decide) ((mem_Tset ..).1 p))
lemma waved_stand (x:Site n)(i:SU.Slot): withinM (modesIn n {node x}) (Waved x i):=within_basis _ _ ((modes_at ..).2 (mem_singleton_self _))
def astral (o:Seat n)(t:ℕ) (r:Fin k→Site n)(j:ℕ)(M:Tulip.Male)(a:SU.Slot)(k0:Fin k)(x:Pane n):= acts (star (chartG n o x)) (sparkUp (sp false j M (1:Pane n)) (modesIn n (VolumeX r)) (modesIn n (BlockP t o)) (acts (chartG n o x) (Waved (r k0) a)))
lemma astral_cont (o:Seat n)(x:SU.Slot)(p:Fin k) : Continuous (astral o d r j M x p):=by unfold astral sparkUp warmth; exact (acts_cont.comp chartG_cont.star).clm_apply ((acts _).continuous.comp ((acts _).continuous.comp ((acts _).continuous.comp ((acts_cont.comp chartG_cont).clm_apply continuous_const))))
variable {t:ℕ}{s:SU.Slot}{u:Seat n}{a:Pane n}
lemma chart_hike (l: IsUnit (Fock.padded (modesIn n (VolumeX r)) (sp false j M (1:Pane n)))) (p:1 ≤ j) (i:Fin k): withinM (labelQ n (family s)) (astral o t r j M s i a):=by
 let x:=tradew n (stampG o a); apply (book_rest (family s) (stampG o a) _).1; unfold astral chartG; rw [act_starUnit]; exact cutShift (labelKick p _ M) l ((book_rest _ _ _).2 (within_basis _ _ (labelAt .. |>.2 rfl)))
private lemma astral_broad(i:Fin k)(s:SU.Slot)(o:Seat n)(p:Pane n): withinM (modesIn n (BlockP t o)) (astral o t r j M s i p):=by apply coverSense (t:=stampG o p)|>.1; unfold astral chartG; rw [act_starUnit]; exact covers_spark
lemma blankPaid (w:VolumeX r ⊆ BlockP t o) (l: IsUnit (Fock.padded (modesIn n (VolumeX r)) (sp false j M (1:Pane n)))) (i:Fin k): withinM (modesIn n (VolumeX r))ᶜ (cardH false (cutM (Tset n)) (astral o t r j M s i a)):=by
 let X:= Waved (r i) s; let Y:=astral o t r j M s i a; let S:=VolumeX r; let F:=stampG o a; let T:=tradew n F; let P:=cutM (Tset n); have hp: trim (1-P) X:= waved_pay ..
 have he:acts (Vo S) Y=X:= by
    have hx: acts T.val (acts (Vo S) Y)=acts T.val X:=by
       rw [act_field _ (gauge_frost _ (stampG o a)),show acts T.val Y= _ from (act_starUnit T (sparkUp (sp false j M (1:Pane n)) (modesIn n S) (modesIn n (BlockP t o)) (acts T.val X)))]
       apply touch_spark l (modes_monotone w); apply (coverSense).2; exact within_basis _ _ ((modes_at ..).2 (mem_image_of_mem (node ∘ r) (mem_univ i)))
    have ht:= congrArg (acts (star T.val)) hx; rwa [act_unit,act_unit] at ht
 apply within_compl.mpr; change acts (Vo S) (acts P Y)=0; rw [←act_mul, (show Vo S*P=P*Vo S from (cutLane (modesIn n S) (Tset n)).eq),act_mul,he]; unfold trim at hp; rw [act_sub,act_one,sub_eq_self] at hp; exact hp
lemma starAgrees (w:VolumeX r ⊆ BlockP t o)(v₀:Fin k)(x y:Pane n)(p:Lattice.Agrees (BlockP t o) x y): astral o t r j M s v₀ x=astral o t r j M s v₀ y:=by
 let F:=stampG o x; let G:=stampG o y; let X:= tradew n F; let Y:=tradew n G
 let D:= BlockP t o; have hp(z:Seat n)(v:z∈ D): F z=G z:= stampG_consistent o p v
 let S:=modesIn n (VolumeX r); let T:=modesIn n D
 let x0:=Waved (r v₀) s; let v':=sparkUp (sp false j M (1:Pane n)) S T (acts (chartG n o x) x0);
 have hg:acts Y.val x0=acts X.val x0:= agreePick D _ _ hp (within_basis _ _ ((modes_at ..).2 (w (mem_image_of_mem (node ∘ r) (mem_univ v₀))))) -- tune arg f
 change acts (star X.val) v'=acts (star Y.val) (sparkUp (sp false j M (1:Pane n)) S T (acts Y.val x0)); rw [hg]
 suffices hx:acts Y.val (acts (star X.val) v')= v' by change _=acts (star Y.val) v'; nth_rw 2 [←hx]; rw [act_unit]
 rw [agreePick D F G hp (show withinM T (acts (star X.val) v') from astral_broad v₀ s o x),act_starUnit]
-- simplify fixed delivered term
abbrev Forward (o:Seat n)(t:ℕ)(r:Fin k→Site n)(j:ℕ)(M:Tulip.Male)(s:SU.Slot)(i:Fin k)(x:Pane n):=cardH false (cutM (Tset n)) (astral o t r j M s i x)
lemma out_turn(i:Fin k)(x:Pane n): withinM (modesIn n (BlockP t o)) (Forward o t r j M s i x):=within_cut _ _ (astral_broad i s o x) -- arg order
lemma out_bank(l: IsUnit (Fock.padded (modesIn n (VolumeX r)) (sp false j M (1:Pane n)))) (p:1 ≤ j) (i:Fin k)(x:Pane n): withinM (labelQ n (family s)) (Forward o t r j M s i x):= within_cut _ _ (chart_hike l p i)
lemma out_half(i:Fin k)(x:Pane n): withinM (Tset n) (Forward o t r j M s i x):= raft_trim false (cutM_idp _) _

def bloomers(o:Seat n)(t:ℕ)(r:Fin k→Site n)(j:ℕ)(M:Tulip.Male)(s:SU.Slot)(i:Fin k): Mark n:= fun x=> handy false (Tset n) (Waved (r i) s) (astral o t r j M s i x.1)
lemma nourish (o:Seat n)(t:ℕ)(i:Fin k)(x:Fields n) : bloomers o t r j M s i x=1+remove (Waved (r i) s)* create (Forward o t r j M s i x.1):= rfl
lemma oneCake {i:Fin k}(w:VolumeX r ⊆ BlockP t o): AtSupport false (BlockP t o) (bloomers o t r j M s i):=by
 let f:= Forward o t r j M s i; constructor
 · apply Push.SectorMeasure.Env.compact; simp_rw [show bloomers o t r j M s i =fun x=>1+remove (Waved (r i) s)* create (f x.1) from funext (fun x=>nourish ..)]; have h:Continuous f:=(acts (hand false (cutM (Tset n)))).continuous.comp (astral_cont ..) -- tune
   exact continuous_const.add (continuous_const.mul (create_cont.comp (h.comp continuous_fst))) -- create CLM?
 · intro x y p _; unfold bloomers; rw [starAgrees w i x.1 y.1 p]
 intro x; rw [nourish]; exact Fine.one.add ((fine_remove (Waved (r i) s) (by unfold withinM; rw [dim_cut]; exact waved_pay ..) (within_basis _ (Poi (r i) s) ((modes_at ..).2 (w (mem_image_of_mem (node ∘ r) (mem_univ i)))))).grow (fine_create _ (out_half ..) (out_turn ..)))

abbrev race (k:ℕ): List (Fin k):= List.ofFn id
def repast (o:Seat n)(t:ℕ)(r:Fin k→Site n)(j:ℕ)(M:Tulip.Male)(s:SU.Slot): Cliplet n k:= ⟨BlockP t o,node ∘ r,false,((race k).map (bloomers o t r j M s)).prod⟩
lemma tasteR (o: Seat n)(t:ℕ)(x:Fields n): (repast o t r j M s).frame x=((race k).map (fun i=> handy false (Tset n) (Waved (r i) s) (astral o t r j M s i x.1))).prod:=by
 change (((race k).map (bloomers o t r j M s)).prod) x=_
 generalize race k=L; induction L with|nil=>rfl|cons i L ih=> simp only [List.map_cons,List.prod_cons,Pi.mul_apply,ih]; rfl
lemma repast_one (o:Seat n)(t:ℕ)(x y:Fields n)(p:x.1=y.1): (repast o t r j M s).frame x=(repast o t r j M s).frame y:= by rw [tasteR,tasteR,p]
lemma feastReady (o:Seat n)(t:ℕ) : Continuous (repast o t r j M s).frame:=by
 change Continuous (((race k).map (bloomers o t r j M s)).prod)
 generalize race k=L; induction L with
 | nil=> exact continuous_const
 | cons i L ih =>
    apply Continuous.mul _ ih; let f:= Forward o t r j M s i; have hp:Continuous f := (acts (hand false (cutM (Tset n)))).continuous.comp (astral_cont o s i); unfold bloomers; change Continuous (fun x:Fields n=>1+remove (Waved (r i) s)*create (f x.1)); exact continuous_const.add (continuous_const.mul (create_cont.comp (hp.comp continuous_fst)))
lemma repastPrize {w₀ c f l τ γ} (p:Sparse l (VolumeX r))(d: Injective (node ∘ r))(g:Lattice.halo (w₀+l+1) (VolumeX r)⊆ BlockP c o)(w:c+1 ≤ f) (U:∀ V:Pane n, Disjoint (BlockP f o) (flags τ V) → Rightful (BlockP c o) (gauge (stampG o V) V) 1 γ): Cliplet.Perron j M w₀ l f γ τ (repast o c r j M s):=by
 let C:= BlockP c o; have he: VolumeX r ⊆ C:= subset_trans (halo_subset ..) g; refine ⟨?_,d,p,g,fun x=>?_⟩
 · change AtSupport false C (((race k).map _).prod); generalize race k=L; induction L with|nil=>exact AtSupport.oneM C|cons i L ih=> exact (oneCake (t:=c) (i:=i) he).mulM ih
 refine ⟨stampG o x.1, fun i=> Waved (r i) s,fun i=> astral o c r j M s i x.1,fun t=> U _ (Disjoint.mono_left (Corona.halo_mono le_rfl (singleton_subset_iff.mpr (halo_subset c _ (mem_singleton_self _)))) t),?_,fun i=> waved_stand ..,fun i=>waved_pay ..,fun i=>waved_const ..,fun i=> act_starUnit (tradew n (stampG o x.1)) _⟩ -- syntax halo_subset
 rw [tasteR]; unfold race Cliplet.xpert; rw [List.map_ofFn]; rfl
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.repastPrize
#print axioms YM.CF.Pannier.Chancel.out_bank
