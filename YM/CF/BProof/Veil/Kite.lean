import YM.CF.BProof.Veil.Ink
import YM.CF.BProof.Oasis.Log
import YM.CF.BProof.Hero.Bill
import YM.CF.BProof.Tape.Ark
import YM.CF.BProof.Tape.Shelf
/-! Local reading space Q on gauge sites. Keep all [Y,Z] outside Mark. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.BProof.Veil
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Skye Spin Branch Hearth Tape Hero
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N:Side}{X D:Type}[MeasurableSpace X][MeasurableSpace D]
section Atom
variable {U V:Type}[Fintype U][DecidableEq U][Fintype V][DecidableEq V] (Y:Support N→ Finset V) (d:X)
def clean(S:Support N)(F:V→ X)(i:V):= if i∈ Y S then F i else d
lemma clean_eq(S:Support N)(F H: V→X) : clean Y d S F =clean Y d S H ↔ ∀ i∈Y S,F i=H i:=by constructor; intro h i v; simpa only [clean,v,if_true] using congrFun h i; intro h; funext i; unfold clean; split; exact h _ ‹_›; rfl
lemma clean_c(S:Support N) : Measurable (clean Y d S):=by apply measurable_pi_lambda; intro i; unfold clean; split; exact measurable_pi_apply _; exact measurable_const
end Atom
variable (S:Support (More N))
def pine(N:Side) : RecN (More N) (Pane N) where
 snap:= clean leaks 1
 act:= Lattice.gauge
 one x:= by ext1 i; unfold Lattice.gauge; simp only [Pi.one_apply,one_mul,inv_one,mul_one]
 comp g h x:=by ext1 i; unfold Lattice.gauge; simp only [Pi.mul_apply, mul_inv_rev,mul_assoc]
 trace_h {S T} e {x y} p:=(clean_eq leaks 1 T x y).mpr (fun i h=> (clean_eq leaks 1 S x y).mp p i (leaks_up e h))
 tw {S} g {x y} p:=by rw [clean_eq ..] at *; intro i h; unfold Lattice.gauge; rw [p i h] -- binder tune
 hol T:= clean_c ..
 spin:=by apply measurable_pi_lambda; intro i; unfold uncurry Lattice.gauge; fun_prop
lemma pine_eq {F G: Pane N}: (pine N).agree S F G ↔ Agrees (↑S) F G:=by rw [RecN.agree,pine]; dsimp only; rw [clean_eq]; exact ⟨fun h i a b=> h i (mem_filter.mpr ⟨mem_univ _,a,b⟩),fun h i g=>h i (mem_filter.mp g).2.1 (mem_filter.mp g).2.2⟩
def shoots (N:Side) : RecN (More N) (Piles N) where
 snap T S := S.filter fun i=> node i∈T
 act:=fun _=>id
 one _:=rfl
 comp _ _ _:=rfl
 trace_h {T U} u {x y} d:=by
    ext i; simp only [mem_filter]; by_cases h:node i∈ U; swap; simp [h]
    have he:= Finset.ext_iff.mp d i; simp only [mem_filter,u h,and_true] at he; rw [he]
 tw _ {x y} :=id
 hol _:= measurable_of_countable _
 spin:=measurable_snd
lemma shoots_rule{x y:Piles N}:(shoots N).agree S x y ↔ ∀ i∈S,i∈spot x ↔ i∈spot y:=by
 constructor; intro h i v; have he {x y:Piles N} (h:(shoots N).agree S x y) (u:i∈spot x): i∈spot y:=by
   obtain ⟨j,hp,p⟩:=mem_image.mp u; refine mem_image.mpr ⟨j,?_,p⟩; have he:j∈x.filter (fun i=>node i ∈ S):= mem_filter.mpr ⟨hp,p.symm ▸ v⟩; exact (mem_filter.mp (show j∈ (shoots N).snap S y from h ▸ (show j∈ (shoots N).snap S x from he))).1
 exact ⟨he h,he (Eq.symm h)⟩
 intro t; unfold RecN.agree shoots; ext i; by_cases h:node i∈S; swap; simp [h]
 simp only [mem_filter,h,and_true]; rw [←spot_spec x,←spot_spec y]; exact t _ h -- tune d
-- threads include [-1,2] collars from deriv extension
lemma motion_cont : Continuous (fun i:E × Stamp=> motion i.1 i.2):=by -- tune measurable ambient instances Op Stamp
 unfold motion Fock.congrC; exact ((matter_cont.comp continuous_fst).mul continuous_snd).mul ((matter_cont.comp continuous_fst).matrix_transpose)
lemma piFamily (I:Type)(h:X→ D→D)(p:Measurable (uncurry h)): Measurable (fun (x:(I→ X)×(I→D)) i=> h (x.1 i) (x.2 i)):=by apply measurable_pi_lambda; intro i; exact p.comp (((measurable_pi_apply (X:=fun _=>X) i).comp measurable_fst).prodMk ((measurable_pi_apply (X:=fun _=>D) i).comp measurable_snd))
def tickThread(g:E)(T: Thread): Thread:=fun k=>⟨fun x=> motion g (T k x),by unfold motion Fock.congrC; fun_prop⟩
lemma heroC {J V C₁ D:Type}[TopologicalSpace V][TopologicalSpace C₁][TopologicalSpace D][LocallyCompactSpace V](m:C₁→D→D)(hm:Continuous (uncurry m))(F:C₁ × (J→ C(V,D))→J→ C(V,D))(p:∀ x t j,F x t j=m x.1 (x.2 t j)) : Continuous F:=by
    apply continuous_pi; intro t; apply ContinuousMap.continuous_of_continuous_uncurry; change Continuous (fun x:(C₁ × (J→ C(V,D))) × V=>F x.1 t x.2); simp_rw [p]; exact hm.comp (f:=fun x:(C₁ × (J→ C(V,D)))×V=>(x.1.1, x.1.2 t x.2)) ((continuous_fst.comp continuous_fst).prodMk (((continuous_apply t).comp (continuous_snd.comp continuous_fst)).eval continuous_snd))
lemma mTick: Measurable (uncurry tickThread):= (heroC (J:=Key) motion motion_cont _ (fun _ _ _=>rfl : ∀ (x:E×Thread) t j, tickThread x.1 x.2 t j=motion x.1 (x.2 t j))).measurable
lemma sweeps_m(N:Side) : Measurable (uncurry (sweepThread (N:=N))):=by
 exact piFamily (Site (More N)) tickThread mTick
def curving(N:Side): RecN (More N) (Throne N) where
 snap:= clean id 0
 act:= sweepThread
 one x:=by funext i k; ext1 t; exact congrFun motion_one _
 comp g h x:=by funext i k; ext1 t; exact motion_seq ..
 trace_h {T U} u {x y} d:= (clean_eq ..).mpr (fun i h=> (clean_eq ..).mp d i (u h))
 tw {S} g {x y} h:=(clean_eq id 0 S _ _).mpr (fun i hi=> by have hp:= (clean_eq id 0 S x y).mp h i hi; funext k; ext1 t; change motion _ (x i k t)= motion _ (y i k t); rw [hp])
 hol T:=clean_c ..
 spin:=sweeps_m N
lemma curve_rule{x y:Throne N}: (curving N).agree S x y ↔ ∀ i ∈ S,x i=y i:= clean_eq ..
def tent(N:Side): RecN (More N) (Stun N) where
 snap:= clean id apex
 act:= feast
 one x:=by funext i; exact congrFun Hero.scaled_one _
 comp g h x:=by funext i; exact Hero.scaled_seq ..
 trace_h {T U} u {x y} d:= (clean_eq ..).mpr (fun i h=> (clean_eq ..).mp d i (u h))
 tw {S} g {x y} h:= (clean_eq ..).mpr (fun i hi=>by unfold feast; rw [(clean_eq ..).mp h i hi])
 hol T:=clean_c ..
 spin:=by
    exact piFamily (Site (More N)) scaledV scaled_cont.measurable
lemma tent_eq{x y:Stun N}: (tent N).agree S x y↔ ∀ i∈ S,x i=y i:=clean_eq ..
-- composite relations
abbrev Window (N:Side):= (Pane N × Piles N) × Throne N
def window(N:Side): RecN (More N) (Window N):=((pine N).together (shoots N)).together (curving N)
lemma paired {A:RecN (More N) D}{B:RecN (More N) X}{x y:D×X}: (A.together B).agree S x y ↔ A.agree S x.1 y.1 ∧ B.agree S x.2 y.2:= iff_of_eq (Prod.mk.injEq ..) -- tune
abbrev Quiet(N:Side):=Pane N × Window N
def quiet(N:Side):= (pine N).together (window N)
-- reserve spin + X path separate from covariance argument
abbrev World(N:Side):= Quiet N × Stun N
def world(N:Side):=(quiet N).together (tent N)
end YM.CF.BProof.Veil
