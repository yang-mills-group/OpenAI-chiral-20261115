import GaugeFieldConstruction.HailMag
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat
open Etch
namespace Weir
section fee
variable {K:Calibration}{I:Type*}{σ:Cover}{W:ℤ}{F:I→Family K}{o:I → Cover}{L J: List (Raft K I)}{m n:Side}{S:I→Finset Cover}
local notation "V"=> Vibro F o σ W n
variable {G:I→ℝ}
variable {D:ℝ}{X:Mark (K.c m)→ℂ}{L':Loom (K.c m)}
private lemma buoy_bdd (q:ℝ)(h:0<q)(v:∀ i,q≤G i):(q^L.length)≤buoy G L:=by
 induction L with
 | nil=> simp
 | cons a L ih=> rw[List.length_cons,pow_succ']; exact mul_le_mul (v a.ink) ih (pow_pos h _|>.le) (le_trans h.le (v _))
private lemma pond_bdd {A c:ℝ}(Q:1≤A)(R: 0<c)(Rc:c≤1)(h₀:∀ i,c≤G i)(t:∀ i,pay (F i) A)(p:∀ i,InTest K true (S i) false (F i))(h:∀ i,Barn K W σ (o i) (S i))(v:V L)(e:Metered K m L' X D): Wplus G X L ≤ (Real.exp (D*(m.val:ℝ)^4)*A^((More n).val^4)) / c^((More n).val^4) :=by
 unfold Wplus MatX
 have hv:L.length≤(More n).val^4:=vibro_length v
 apply le_trans (div_le_div_of_nonneg_right ?_ ( buoy_pos (L:=L) (fun i=>lt_of_lt_of_le R (h₀ i))|>.le)) (div_le_div_of_nonneg_left _ (pow_pos R _) ((pow_le_pow_of_le_one R.le Rc hv).trans (buoy_bdd c R h₀)))
 · have z:A^L.length≤A^((More n).val^4):=pow_le_pow_right₀ Q hv; exact (bill e (tow_test p h v) _ (tow_paid t v)).trans (mul_le_mul_of_nonneg_left z (Real.exp_pos _).le)
 exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith only [Q]) _)
lemma buoy_all {y':I}(g:∀ a∈L,a.ink=y') :buoy G L=G y'^L.length:=by
 induction L with
 | nil=> simp
 | cons a L ih=>
    have h:=ih (fun x h=> g x (List.mem_cons_of_mem _ h))
    change G a.ink*buoy G L= _
    rw[List.length_cons,pow_succ',h,g a (by simp)]
-- variant directly from full sharp-price bound repeated label
lemma quake {A c:ℝ}(Q:1≤A)(R:0<c)(Rc:c≤1)(h₀:∀ i,c≤G i)(t:∀ i,pay (F i) A)(p:∀ i,InTest K true (S i) false (F i))(h:∀ i,Barn K W σ (o i) (S i))(e:Metered K m L' X D)(w:LatticeFare K m n W σ)(r:∀ J,V J→J.length=(n.val*2)^4→∀ i, (∀ a∈J,a.ink=i)→ MatX X J≤ G i^((n.val*2)^4))(j:V L):MatX X L≤buoy G L:=by
 have ca(i):0<G i:= lt_of_lt_of_le R (h₀ i)
 let S':Set ℝ:= {x | ∃ L,V L∧ x=Wplus G X L}
 let M₀:= sSup S'
 have hv:1∈S':= by
    refine ⟨[],⟨fun _ y=>by simp at y,List.nodup_nil⟩,?_⟩
    simp only [Wplus,MatX,wharf_nil,Pi.one_apply, buoy_nil,div_one,e.unit,norm_one]
 have he:Set.Nonempty S':=⟨_,hv⟩
 have z₀:BddAbove S':=by
    refine ⟨(Real.exp (D*(m.val:ℝ)^4)*A^((More n).val^4)) / c^((More n).val^4),?_⟩; rintro x ⟨L,v,rfl⟩; exact pond_bdd Q R Rc h₀ t p h v e
 have h₁:1≤M₀:=le_csSup z₀ hv; have m₀:0<M₀:=zero_lt_one.trans_le h₁
 let M(L:List (Raft K I)):= Wplus G X L / M₀
 have h2(L): V L→ M L≤1:=fun v=> (div_le_one m₀).2 (le_csSup z₀ (show Wplus G X L∈S' from ⟨L,v,rfl⟩))
 have hM:LitBank F o σ W m n M:=by
    refine ⟨w,(fun L v=>⟨div_nonneg (div_nonneg (norm_nonneg _) (buoy_pos ca).le) m₀.le,h2 L v⟩),?_⟩
    intro j b s k L v
    unfold M; rw[div_pow,div_mul_div_comm,pow_two M₀]; exact div_le_div_of_nonneg_right (tow_rift j b w p h v e k ca) (mul_self_nonneg M₀)
 let K':ℕ:=2^(n.val*4); have ht:0<K':=by unfold K'; positivity
 let C:Set ℝ:={x| (x/M₀)^K' ≤1/M₀}
 have hi:IsClosed C:=isClosed_le (g:=fun _=>1/M₀) (by fun_prop) continuous_const
 have hx:S'⊆ C:=by
    rintro x ⟨L,u,rfl⟩; change (M L)^K' ≤1/M₀
    by_cases d:L=[]
    · subst L; have hi:Wplus G X ([]:List (Raft K I))=1:=by simp only [Wplus,MatX,wharf_nil,Pi.one_apply,buoy_nil,div_one,e.unit,norm_one]
      apply (pow_le_pow_of_le_one (hM.paid [] u).1 (hM.paid [] u).2 (show 1≤K' from ht)).trans
      unfold M; rw [pow_one,hi]; -- tune
    obtain ⟨x,t⟩:=List.exists_mem_of_ne_nil _ d
    obtain ⟨J,VJ,a,z⟩:= hM.splash u (show Keeps n x.ink x.posC L from ⟨x,t,rfl,rfl⟩) univ
    rw[card_univ,show Fintype.card Axis=4 from card_fin ..] at a
    obtain ⟨q',T⟩:= Cabo.flush z VJ
    apply a.trans
    refine div_le_div_of_nonneg_right ((div_le_one (buoy_pos ca)).2 ?_) m₀.le
    rw[buoy_all T,q']; exact r J VJ q' x.ink T
 have hx: (M₀/M₀)^K' ≤ 1/M₀:=closure_minimal hx hi (csSup_mem_closure he z₀)
 rw[div_self m₀.ne',one_pow] at hx
 have H₀:M₀≤ 1:= (one_le_div m₀).1 hx
 exact (div_le_one (buoy_pos ca)).1 ((le_csSup z₀ (show Wplus G X L∈S' from ⟨L,j,rfl⟩)).trans H₀)
#print axioms quake
end fee
end Weir
end YM.CF.Buffered.Afterglow.Tower.SlabMark
