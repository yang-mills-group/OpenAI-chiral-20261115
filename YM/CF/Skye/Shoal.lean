import YM.CF.Skye.Pine
import YM.PCalc.Chart
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n m:Side}{u d:ℝ}{r:ℕ}
variable (G:Ratio n m)(h:Odd G.count.val)
def stepsY(x:Seat m)(t:Step): Walk:= if (ratio G).parent x=(ratio G).parent (x+t.vec) then [] else [t]
def dropY (x:Seat m): Walk→ Walk
| []=> []
| t::l=>stepsY G x t ++ dropY (x+t.vec) l
lemma drop_size (x:Seat m)(w:Walk): (dropY G x w).length ≤ w.length:=by induction w generalizing x; simp [dropY]; next t l ih=> rw [dropY,List.length_append,List.length_cons]; have hx:=ih (x+t.vec); unfold stepsY; split_ifs <;> simp only [List.length_cons,List.length_nil] <;> omega
include h in
lemma stepP (V:Pane n)(x:Seat m)(t:Step): t.read (Precision.replica (ratio G) V) x=travel V ((ratio G).parent x) (stepsY G x t) ∧ (ratio G).parent (x+t.vec)=stop ((ratio G).parent x) (stepsY G x t):=by
 let g:=ratio G; have h':Odd g.count.val:=h
 cases t with | mk i b=>
  cases b
  · let l:=stepsY G x (posDir i); change Precision.replica g V (x,i)=travel V (g.parent x) l ∧ g.parent (x+step i)=stop (g.parent x) l
    have he:l=(if g.parent x=g.parent (x+step i) then [] else [posDir i]):=rfl; rw [he]
    by_cases z:g.parent x=g.parent (x+step i); · exact ⟨(if_pos z.symm).trans (by rw [if_pos z]; rfl),by rw [if_pos z]; exact z.symm⟩
    rw [Precision.replica,if_neg  (Ne.symm z), if_neg z]; have hv:=g.parents_hop h' x i; split at hv
    · simp [travel,stop]; exact hv
    exact False.elim (z hv.symm)
  let l:=stepsY G x (negDir i); change _⁻¹ = travel V (g.parent x) l ∧ g.parent (x+ -step i)=stop (g.parent x) l
  change (Precision.replica g V (x-step i,i))⁻¹=_∧_
  rw [show l=(if g.parent x=g.parent (x+ -step i) then [] else [negDir i]) from rfl,←sub_eq_add_neg, Precision.replica]; dsimp only; rw [sub_add_cancel]; by_cases z:g.parent x=g.parent (x-step i)
  · rw [if_pos z,if_pos z]; exact ⟨inv_one,z.symm⟩
  rw [if_neg z,if_neg z]; have hx:=g.parents_hop h' (x-step i) i; rw [sub_add_cancel] at hx; split at hx; · change (V _)⁻¹= travel V (g.parent x) [negDir i] ∧ g.parent _=g.parent x + -step i; rw [hx]; simp [travel]
  exact False.elim (z hx)
include h
lemma foldT(V:Pane n)(x:Seat m)(l:Walk): travel (Precision.replica (ratio G) V) x l=travel V ((ratio G).parent x) (dropY G x l) ∧ stop ((ratio G).parent x) (dropY G x l)= (ratio G).parent (stop x l):=by
 induction l generalizing x with
 | nil=> exact ⟨rfl,rfl⟩
 | cons i l ih=> rw [dropY, stop,travel, travel_append,stop_append,←(stepP G h V x i).2,(stepP G h V x i).1,(ih (x+i.vec)).1]; exact ⟨rfl,(ih (x+i.vec)).2⟩
omit h in
private lemma casts {n:Side}(x y:ℤ)(u:ℕ)(p:x.natAbs≤u)(q:y.natAbs≤u)(k:2*u < n.val)(v:(x:Per n)=↑y): x=y:=by
 have he: (n.val:ℤ) ∣ x-y:=by rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [v,sub_self]
 by_contra g; have ho:= Int.natAbs_le_of_dvd_ne_zero he (sub_ne_zero.mpr g); omega
lemma newt (V:Pane n)(x: reach n)(k:2*G.count.val<(More n).val): travel (Precision.replica (ratio G) V) ((ratio G).embed x.1) (pathL G x.2)=V x:=by
 let y:Seat m:= (ratio G).embed x.1; let l:=dropY G y (pathL G x.2)
 have he:=foldT G h V y (pathL G x.2); rw [show (ratio G).parent y=x.1 from Ratio.embed_parent ..,stopG,Ratio.embed_parent] at he; rw [he.1]
 have hx:l= List.replicate l.length (posDir x.2):=by
    have hh':pathL G x.2=List.replicate G.count.val (posDir x.2):=by simp [pathL,straight,posDir]
    have hh (y:Seat m)(i:ℕ):let l:=dropY G y (List.replicate i (posDir x.2)); l=List.replicate l.length (posDir x.2):=by
       induction i generalizing y with
       | zero=> rfl
       | succ i ih=> dsimp only; rw [List.replicate_succ,dropY, List.length_append]; unfold stepsY; split
                     · rw [List.length_nil,Nat.zero_add,List.nil_append]; exact ih _
                     next l=> rw [List.length_singleton,Nat.one_add,List.replicate_succ]; exact congrArg (List.cons (posDir x.2)) (ih _)
    unfold l; rw [hh']; exact hh ..
 have hu:l.length=1:=by
    have hv: stop x.1 l=x.1+step x.2:=he.2
    rw [hx] at hv
    have hW(i:ℕ)(b:Seat n): stop b (List.replicate i (posDir x.2))=b+ i • step x.2:=by induction i generalizing b; simp [stop]; next i ih=> rw [List.replicate_succ,stop, ih, Step.vec_pos, add_smul,one_smul]; abel
    rw [hW] at hv; have ht:=drop_size G y (pathL G x.2); rw [pathGL] at ht; change l.length ≤ G.count.val at ht
    have he: ((l.length:ℕ):ℤ)=1:=by refine casts (n:=More n) _ _ _ (by simp [ht]) (by exact G.count.property) k ?_; exact_mod_cast (by simpa [nsmul_eq_mul] using congrFun (add_left_cancel hv) x.2 : (l.length:Per (More n))=1)
    exact_mod_cast he
 rw [show dropY _ _ _=l from rfl,hx,hu]; simp [travel] -- occurrence
lemma lastZ(V:Pane n)(k:8<(More n).val)(x i j)(v:i ≠ j):let l:=dropY G x (square i j); l.length ≤ 4∧ stop (0:Cover) l=0:=by
    intro l; have ht:l.length≤4:=drop_size G x (square i j); have hp:= (foldT G h V x (square i j)).2; rw [square_stop] at hp
    let v:=(ratio G).parent x; have hp'(w:Walk)(a b: Seat n):stop (a+b) w=a+stop b w:=by induction w generalizing b; rfl; next i w ih=> rw [stop,add_assoc,ih]; rfl
    have hs:wrap (More n) (stop (0:Cover) l)=0:=by rw [wrap_stop_cover,map_zero]; apply add_left_cancel (a:=v); rw [←hp',add_zero]; exact hp
    constructor; exact ht; funext j; refine casts (n:=More n) _ _ 4 ?_ (by simp) k ?_; · simpa using ((coord_size 0 l j).trans ht)
    simp; exact (congrFun hs j) -- tune
lemma paid_plaq (V:Pane n)(g:0≤u)(k:8<(More n).val){I:Type*}[Fintype I][DecidableEq I](F:E→*UNI I)(p:PlaqBound F V u) : PlaqBound F (Precision.replica (ratio G) V) (64*u):=by
    intro x i j v; rw [(foldT G h V x (square i j)).1]; obtain ⟨k,hv⟩:=lastZ G h V k x i j v; let L:=dropY G x (square i j); have hx:=near_hop g p ((ratio G).parent x) L [] hv; unfold Cube.cmp at hx; rw [travel, map_one] at hx; have hh:‖(F (travel V ((ratio G).parent x) L)).val -1‖ ≤ 4*(L.length:ℝ)^2*u:=(by simpa using hx); refine hh.trans ?_; apply mul_le_mul_of_nonneg_right _ g; nlinarith [show (L.length:ℝ) ≤ 4 from by exact_mod_cast k, show 0 ≤ (L.length:ℝ) by positivity]
lemma wingJ (V:Pane n)(p:Guard V u)(g:0≤u)(k:8<(More n).val) : Guard (Precision.replica (ratio G) V) (64*u):=
 ⟨paid_plaq G h V g k firstF p.1,paid_plaq G h V g k matter p.2⟩
end YM.CF.Skye
