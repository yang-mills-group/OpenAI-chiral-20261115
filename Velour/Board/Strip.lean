import Velour.Board.Motion
/-! Whole strips: booking endpoints accounted on the nose. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option maxHeartbeats 1200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
open SatinVerification

variable {K:Calibration} {w:ℕ} {o:Cell} {f:Family K}
def stripL(j:Axis)(a:ℤ):Cell := fun i=> if i=j then a else 0
def stripU(j:Axis)(b:ℤ):Cell := fun i=> if i=j then b else 1
def Strip (w:ℕ)(o:Cell)(f:Family K)(j:Axis)(a b:ℤ)(c:ℕ)(x:Family K) : Prop :=
 ∃ l:List (Tile K), Paved w o f l (stripL j a) (stripU j b) ∧ l.length=c ∧ Representation l=x
variable {j:Axis}{a b a' b':ℤ}{n m:ℕ}{x y:Family K}
lemma join_lines
 (p:Strip w o f j a b n x)(q:Strip w o f j b b' m y)
 (A:a≤b) (B:b≤b'):Strip w o f j a b' (n+m) (x*y):=by
 obtain ⟨l,r,rfl,rfl⟩:=p; obtain ⟨t,s,rfl,rfl⟩:=q
 exact ⟨_, pavingJoin r s j (by simp [stripL,stripU])
    (fun k=>by unfold stripL; split_ifs <;> omega)
    (fun k=>by unfold stripU; split_ifs <;> omega),List.length_append,rep_append ..⟩

lemma turned_line (p:Strip w o f j a b n x)(d:ℤ):
 Strip w o f j (d-b) (d-a) n (mirror K j (PaneCut K w o j d) x):=by
 obtain ⟨l,r,rfl,rfl⟩:=p
 have h:=pavingMir r j d
 have e:cutOver (stripL j a) j (d-stripU j b j)=stripL j (d-b):=by
    ext i; unfold cutOver stripU stripL; split_ifs <;> simp_all
 have g:cutOver (stripU j b) j (d-stripL j a j)=stripU j (d-a):=by
    ext i; unfold cutOver stripU stripL; split_ifs <;> simp_all
 rw [e,g] at h; exact ⟨_,h,List.length_map _,rep_mirror ..⟩
variable (e:o j=0)
include e
lemma along_line (p:Strip w o f j a b n x)(v:ℤ):
 Strip w o f j (v+a) (v+b) n (relocate K j (w*v) x):=by
 have h:=turned_line (turned_line p 0) v
 simpa only [PaneCut,e,mul_zero,zero_add,gaugeT_zero,zero_sub,sub_neg_eq_add,relocate,chime] using h

variable (w o f)
lemma toward_line (n:ℕ):Strip w o f j 0 1 1 (toward K j w f n):=by
 induction n with
 | zero=>
    refine ⟨[⟨0,f⟩],?_,rfl,by simp [Representation,toward]⟩
    constructor
    · simp only [List.mem_singleton,forall_eq]; exact Transit.here
    · simp
    · intro _ h; rw [List.mem_singleton] at h; subst h; intro i
      simp [stripL,stripU]
 | succ n ih=>
    have h:=turned_line ih 1
    rw [PaneCut,e,mul_one,mul_zero,zero_add,sub_self,sub_zero] at h
    exact h

lemma lace_line (n:ℕ): Strip w o f j 0 n n (lace K j w f 1 n):=by
 induction n with
 | zero=> refine ⟨[],⟨by simp,by simp,by simp⟩,rfl,rfl⟩
 | succ n ih=>
    have q :=along_line e ih 1
    rw [mul_one,add_zero] at q
    have h:=join_lines (toward_line w o f e n) q (by omega) (by omega)
    rw [add_comm (1:ℤ),add_comm (1:ℕ)] at h
    rw [Nat.cast_succ]; exact h

lemma chambers_line (n:ℕ)(v:ℤ):
 Strip w o f j (v-n) (v+n) (2*n) (chambers j w (w*v) f 1 n):=by
 have hp:=lace_line w o f e n
 have q:=turned_line hp 0
 rw [sub_self,zero_sub,PaneCut,e,mul_zero,mul_zero,gaugeT_zero,zero_add] at q
 have h:=along_line e (join_lines q hp (by omega) (by omega)) v
 rw [← sub_eq_add_neg,←two_mul] at h
 exact h
lemma banner_line (n:ℕ)(v:ℤ):
 Strip w o f j (v-3*n) (v+n) (4*n) (banner j w (w*v) n f):=by
 let d:=2*(v-n)
 have hp := chambers_line w o f e n v
 have q := turned_line hp d
 rw [show d-(v+n)=v-3*n by unfold d; ring,show d-(v-n)=v-n by unfold d; ring,
     PaneCut,e,mul_zero,zero_add,show w*d=cliff w (w*v) n by unfold d cliff; ring] at q

 rw [show 4*n=2*n+2*n by omega]
 exact join_lines q hp (by omega) (by omega)

end YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard

