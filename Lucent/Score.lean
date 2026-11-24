import YM.SU5.WindTorque.Turbine
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

/-! # A quoter interface. Templates keep their shape as the pitches,
arm lengths, colors, positions, seasons and even coupling samplers change.
carries generalized *Wake* electrodes. -/

abbrev Pig := SU.group.ColorIndex
/-- First index ties to a Wind Staff, or a fee-free (unused) dummy staff. -/
abbrev Tint (I : Type) := I × Pig
/-- upper species index, then lower -/
abbrev Loop (I : Type) := I × SU.Slot × SU.Slot


/-- Includes balanced gauge-singlets composed of arbitrary products across
arbitrary appointments. Tint may be repeated or tiled at the same prices as a
different Tint (e.g., separate W-charge and encoding slots in orientation work). -/
structure Join (I : Type) where
 flash : List (Tint I)
 loom : List (Loop I)

structure Bill (I : Type) extends Join I where
 k : ℂ

structure Stencil (I : Type) where
 out : List (Bill I)

variable {I J : Type}
abbrev Join.glue (a b:Join I):Join I:= ⟨a.flash++b.flash,a.loom++b.loom⟩
abbrev Bill.glue (a b:Bill I):Bill I:=⟨a.toJoin.glue b.toJoin, a.k*b.k⟩
abbrev Join.grade (a:Join I)(m d:ℕ) := a.flash.length = m ∧ a.loom.length = d
abbrev Bill.grade (a:Bill I)(m d:ℕ) := a.toJoin.grade m d
private def Join.singleton (q : Join I) := (show Bill I from ⟨q,1⟩)

namespace Stencil
def mono (f:List (Tint I))(s:List (Loop I)):Stencil I:= ⟨[(Join.singleton ⟨f,s⟩)]⟩

instance : One (Stencil I) := ⟨mono [] []⟩
instance : Zero (Stencil I) := ⟨⟨[]⟩⟩
instance : Add (Stencil I) := ⟨fun T R=>⟨T.out ++ R.out⟩⟩
instance : SMul ℂ (Stencil I):=⟨fun x T=> ⟨T.out.map fun q=>⟨q.toJoin, x*q.k⟩⟩⟩
instance : Mul (Stencil I):=⟨fun S T=>⟨S.out.flatMap fun q=>T.out.map q.glue⟩⟩

def packList {α:Type*}(L:List α)(F:α→Stencil I):Stencil I:=⟨L.flatMap ((·.out)∘ F)⟩
def pack {α:Type*}(U:Finset α)(F:α→Stencil I):Stencil I:= packList U.toList F
def remake (α:I→J)(T:Stencil I) :Stencil J:=⟨T.out.map fun q=>⟨⟨q.flash.map (Prod.map α id), q.loom.map (Prod.map α id)⟩,q.k⟩⟩
def tailing (L:List (Stencil I)):Stencil I:= L.foldr (·*·) 1

def degree (T:Stencil I) (m d:ℕ): Prop:=∀ q∈T.out,q.grade m d
lemma mono_grade (f:List (Tint I))(s:List (Loop I)): (mono f s).degree f.length s.length:= by intro q h; rw [List.mem_singleton.mp h]; exact ⟨rfl,rfl⟩
variable {S T:Stencil I} {m d m' d':ℕ}
lemma none_g:degree (I:=I) 0 m d:=fun _ h=>(List.not_mem_nil h).elim
lemma one_g:degree (I:=I) 1 0 0:=mono_grade [] []
lemma degree.sum (h:S.degree m d)(k:T.degree m d): (S+T).degree m d:= by
 intro q v; exact (List.mem_append.mp v).elim (h q) (k q)
lemma degree.scale (h:S.degree m d)(v:ℂ):(v • S).degree m d:=by
 intro q l; obtain ⟨b,f,rfl⟩:=List.mem_map.mp (show q∈S.out.map _ from l); exact h b f

lemma degree.mul (h:S.degree m d)(k:T.degree m' d'): (S*T).degree (m+m') (d+d'):=by
 intro q u; change q∈ S.out.flatMap _ at u; obtain ⟨a,z,l⟩:= List.mem_flatMap.mp u; obtain ⟨b,c,rfl⟩:=List.mem_map.mp l; obtain ⟨r,p⟩:=h a z; obtain ⟨w,v⟩:= k b c
 exact ⟨by simp [r,w],by simp [p,v]⟩
lemma degree.remake (h:S.degree m d)(w:I→J): (S.remake w).degree m d:=by
 intro q v; change q∈ S.out.map _ at v; obtain ⟨b,c,rfl⟩:=List.mem_map.mp v; obtain ⟨f,g⟩:=h _ c; exact ⟨(List.length_map ..).trans f,(List.length_map ..).trans g⟩
lemma degree.pack {α:Type*}(U:Finset α)(F:α→Stencil I)(h:∀ j∈U,degree (F j) m d) :
    (pack U F).degree m d:=by
 intro q t; obtain ⟨b,c,d⟩:= List.mem_flatMap.mp t; exact h b (Finset.mem_toList.mp c) q d

variable {R:Type*}[AddCommMonoid R][Module ℂ R]
def quote (h:Join I→R)(S:Stencil I):R:=(S.out.map fun q=> q.k • h q.toJoin).sum
lemma mono_q (f:List (Tint I))(s:List (Loop I))(h:Join I→R):quote h (mono f s)=h ⟨f,s⟩:=by simp [quote,mono,Join.singleton]
variable (h:Join I→R)(S T:Stencil I)
lemma cons_q (q:Bill I)(L:List (Bill I)):quote h {out:=q::L}=q.k • h q.toJoin + quote h {out:=L}:= rfl
lemma none_q:quote h 0=0:= rfl
lemma one_q:quote h 1=h ⟨[],[]⟩:=mono_q [] [] h
lemma sum_q:quote h (S+T)=quote h S+quote h T:=by
 unfold quote; change ((S.out++T.out).map _).sum=_; rw [List.map_append,List.sum_append]
lemma scale_q (v:ℂ):quote h (v • S)=v • quote h S:=by
 cases S with
 | mk L => induction L with
   | nil=> exact (smul_zero v).symm
   | cons j L ih=>
      rw [show v • (⟨j::L⟩:Stencil I) = {out:={j with k:=v*j.k}::(v • (⟨L⟩:Stencil I)).out} from rfl,cons_q,cons_q,mul_smul,smul_add]
      exact congrArg₂ (·+·) rfl ih
lemma pack_q {α:Type*}(U:Finset α)(F:α→Stencil I): quote h (pack U F)=∑ i∈U,quote h (F i):=by
 suffices v:∀ L:List α,quote h (packList L F)=(L.map (quote h ∘ F)).sum by rw [pack,v]; simp -- or use Finset.sum_toList
 intro L; induction L with
 | nil=> rfl
 | cons j L t=>
    rw [show packList (j::L) F=F j+packList L F from ?_, sum_q,t]; · rfl
    simp only [packList,List.flatMap_cons]; rfl

lemma remake_q (u:I→J)(g:Join J→R) : quote g (remake u S)=quote (fun a=>g ⟨a.flash.map (Prod.map u id),a.loom.map (Prod.map u id)⟩) S:=by unfold quote remake; rw [List.map_map]; rfl

/-- Append a probe. No factorization assumption on quotations themselves. -/
lemma mul_q : quote h (S*T)=quote (fun a=>quote (fun b=>h (a.glue b)) T) S := by
 cases S with
 | mk L=> induction L with
   | nil=> rfl
   | cons j L ih=>
      rw [show (⟨j::L⟩:Stencil I)*T= ⟨T.out.map j.glue⟩+ ⟨L⟩*T from ?_, sum_q,ih,cons_q]
      · congr 1; clear L ih; cases T with
        | mk L=> induction L with
          | nil=> exact (smul_zero _).symm
          | cons b L ih=> rw [show (⟨b::L⟩:Stencil I).out=(b::L) from rfl,List.map_cons,cons_q,cons_q,smul_add,←smul_assoc]; exact congrArg₂ (·+·) rfl ih
      change (Stencil.mk ((j::L).flatMap _))=Stencil.mk _; rw [List.flatMap_cons]; rfl

lemma quote_congr (g:Join I→R)(f:∀ q∈ S.out,h q.toJoin=g q.toJoin):quote h S=quote g S:= congrArg List.sum (List.map_congr_left fun q x=>congrArg (q.k • ·) (f q x))


variable {U:Type*}[AddCommMonoid U][Module ℂ U]
lemma quote_lift (g:R→U)(t:g 0=0)(p:∀ x y,g (x+y)=g x+g y)(u:∀ (x:ℂ) y,g (x • y)=x • g y): quote (g ∘ h) S=g (quote h S):=by
 cases S with|mk L=>induction L with|nil=>exact t.symm|cons j L ih=> rw [cons_q,cons_q,p,u,←ih]; rfl
section
variable {V:Type*}[Semiring V][Algebra ℂ V]
lemma quote_mulR (g:Join I→V)(h:∀ x y,g (x.glue y)=g x*g y):quote g (S*T)=quote g S*quote g T:=by
 rw [mul_q]; simp_rw [h];
 have ht(x:Join I) : T.quote (fun y=>g x*g y)=g x*T.quote g := quote_lift g T (g x * ·) (mul_zero _) (mul_add _) (fun a b=>by rw [Algebra.mul_smul_comm]);
 simp_rw [ht]; exact quote_lift g S (· * T.quote g) (zero_mul _) (fun _ _=>add_mul ..) (fun a b=> by rw [Algebra.smul_mul_assoc])
end
end Stencil
