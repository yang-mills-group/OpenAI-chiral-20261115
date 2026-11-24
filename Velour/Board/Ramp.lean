import Velour.Board.Replicate
/-! 
# Clearances survive chess

Travel prices may use extra buffers, even at a coarser rung than
the `Deck` estimate. Check lengths relative to **that** torus.
-/
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

variable {K:Calibration}{w:ℕ}{o:Cell}
def FitsSide (K:Calibration)(w:ℕ) (n:Side)(L U:Cell) := 
 ∀ i,L i ≤ U i ∧ ruler K.B * w * (U i-L i) ≤ 2*(n.val:ℤ)

def Secured (K:Calibration)(w:ℕ)(o:Cell) (d:ℕ) (a:Cell) (x:Cover) :=
 ∀ i,Wall K w o i (a i)+(d:ℤ) ≤ x i ∧ x i+(d:ℤ) ≤ Wall K w o i (a i+1)
variable {n:Side}
/-- Representative can be in arbitrary periods. -/
def Shield (K:Calibration)(w:ℕ)(o:Cell) (d:ℕ) (a:Cell)
    (y:Site (More n)) := ∃ x:Cover, Secured K w o d a x ∧ wrap (More n) x=y
variable {d:ℕ}{a b:Cell}{L U:Cell}
lemma turned (i:Axis)(k:ℤ) (y:Site (More n))(h:Shield K w o d a y):
 Shield K w o d (tipped i k a) ((plane i (PaneCut K w o i k)).anon n y):=by
 obtain ⟨x,p,rfl⟩:=h
 rw [Shape.anno]
 refine ⟨_,fun j=>?_,rfl⟩
 rw [fling_move,tipped]
 by_cases h:i=j
 · subst j
   rw [if_pos rfl,if_pos rfl,sub_add_cancel,show k-a i-1=k-(a i+1) from by ring,
       ←across_wall,←across_wall]
   obtain ⟨q,b⟩:=p i
   omega
 rw [if_neg h,if_neg (Ne.symm h)]; exact p j
lemma windowBound
 {x y:Cover} (i:Axis)
 (h:2*d ≤ y i-x i)
 (q:y i-x i+(2*d:ℤ) ≤ 2*(n.val:ℤ)):
 2*d ≤ separation (wrap (More n) x) (wrap (More n) y):=by
 by_cases g:d=0
 · subst d; simp
 let N:=More n
 have v:(y i-x i).toNat < N.val:=by change _ < n.val*2; omega
 let X:=wrap N x; let Y:=wrap N y
 rw [separation_comm]; change 2*d ≤ pdist (Y-X)
 refine le_trans ?_ (component_le (Y-X) i)
 unfold Lattice.lift
 have hh:(Y-X) i=((y i-x i).toNat:Per N):=by
   have r:y i-x i=((y i-x i).toNat:ℤ):=by omega
   calc (Y-X) i = (y i:Per N) - (x i:Per N):=rfl
        _= _:=by 
           rw [←Int.cast_sub]
           conv_lhs => rw [r]
           rw [Int.cast_natCast]
 rw [hh,ZMod.valMinAbs_natAbs_eq_min,ZMod.val_natCast_of_lt v]
 have hv:N.val=n.val*2:=rfl
 omega

lemma shield_one
 (g:FitsSide K w n L U)
 (pa: RangeAt L U a)(pb:RangeAt L U b)
 (i:Axis)(e:a i<b i)
 {x y:Site (More n)}
 (p: Shield K w o d a x)
 (q: Shield K w o d b y):2*d ≤ separation x y := by
 obtain ⟨u,h,rfl⟩:=p; obtain ⟨v,k,rfl⟩:=q
 specialize h i; specialize k i; specialize pa i; specialize pb i; specialize g i
 have G:= wallMono (K:=K) (w:=w) (o:=o) i
 have l0 := G (show a i+1≤b i by omega)
 have h₁:= G pa.1; have h₂:=G (show b i+1≤U i by omega)
 have h₃:Wall K w o i (U i)-Wall K w o i (L i) ≤ 2*(n.val:ℤ):=by
    unfold Wall; linarith only [g.2]
 exact windowBound i (by omega) (by omega)

lemma separates
 (g:FitsSide K w n L U)
 (pa: RangeAt L U a)(pb:RangeAt L U b)(h:a≠b)
 {x y:Site (More n)}
 (p: Shield K w o d a x)
 (q: Shield K w o d b y):2*d ≤ separation x y := by
 have H:∃i,a i≠b i:=by by_contra! t; exact h (funext t)
 obtain ⟨i,h⟩:=H
 rcases lt_or_gt_of_ne h with u|u
 · exact shield_one g pa pb i u p q
 · rw [separation_comm]; exact shield_one g pb pa i u q p

variable {m:Side}
-- note scalars can depend on rungs
lemma at_coarser {z:ℕ}(v:0<z) (t:(K.c m).val=z*n.val)
 (h:FitsT K m (z*w) L U):FitsSide K w n L U:=by
 intro i; obtain ⟨p,q⟩:=h i
 rw [t,Nat.cast_mul,Nat.cast_mul] at q
 refine ⟨p,le_of_mul_le_mul_right ?_ (show 0<(z:ℤ) by positivity)⟩
 linarith only [q]
lemma coarser_fill {z len:ℕ}(v:0<z)(t:(K.c m).val=z*n.val)
 (h:Fill (pitch K (z*w)) (K.c m).val len):Fill (pitch K w) n.val len:=by
 unfold pitch at h
 rw [show 16*K.B.val*(z*w) = z*pitch K w from by unfold pitch; ring,t] at h

 obtain ⟨a,b⟩:=h
 constructor <;> apply le_of_mul_le_mul_right _ (show (0:ℕ)<z^4 by positivity)
 · linarith only [a]
 · linarith only [b]
lemma scaled_plane {z:ℕ}(i:Axis)(k:ℤ):
 PaneCut K (z*w) (fun i=> z*o i) i k=z*PaneCut K w o i k:=by
 unfold PaneCut gaugeT ruler Heat.gaugeShift; push_cast; ring

end YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard

