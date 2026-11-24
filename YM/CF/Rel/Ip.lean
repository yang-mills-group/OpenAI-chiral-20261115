import YM.CF.Nacre.Shelf
import YM.CF.Braid.Thorn
import YM.CF.Appel.Sat
/-! Scalar reanchoring through leading orders by divergence certificates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
abbrev SpaceX(G:Gauge)(n:Side):= Config G n →ℂ
structure Atom(V: SpaceX G n)(o:Site n)(R:ℕ): Prop where
 fixed (U:Config G n)(g:Site n→G.El): V (gauge g U)=V U
 reads(U W:Config G n): (∀ i: Edge (Site n), separation o i.1 ≤ R→ U i=W i)→ V U=V W
abbrev satX(V:SpaceX G n):= V ∘ represent
variable{f:SpaceX G n}{o:Site n}
-- invariant → shifts only curls
lemma atop_norm (h:Atom f o r)(hs:ContDiffAt ℝ m (satX f) 0)(hp:cFoot m (satX f)) (u:InputZ G n): trim m (satX f) (fullG o u)=trim m (satX f) u:=by
 apply tendsto_nhds_unique_of_eventuallyEq (flares (race o u) hs ((sport o u).of_le le_top) (fullG o u) (roundS ..) (tough ..) hp) ((argent hs).mp hp u); filter_upwards [(wraps o u).filter_mono nhdsWithin_le_nhds] with t ht; simp only [satX, Function.comp_apply,ht,bend,h.fixed]
lemma top_sym(hs: ContDiffAt ℝ m (satX f) 0):Tensor.Sym (cake m (satX f)):=Tensor.coeff_symm hs -- tune
-- direct L map fullG linear from put_sum def
private def hot(G:Gauge)(o:Site n): InputZ G n→L[ℝ]InputZ G n:= LinearMap.toContinuousLinearMap
   {toFun:= fullG o, map_add':=by
       intro a b; funext i; simp only [fullG,Pi.add_apply,Pi.sub_apply]; -- use precision integral or linkSum
       let k:= (Trot n).symm i; have hp (x:Walk):linkSum (collect G (a+b)) o x=linkSum (collect G a) o x+linkSum (collect G b) o x:=by -- via norm function LinearMap
         induction x generalizing o with
         | nil=> simp [linkSum]
         | cons i w hx=> cases i with| mk i h=> cases h <;> simp [linkSum,ask,collect, Step.vec, Step.used,hx] <;> abel
       simp_rw [Font.pure,sap,hp]; unfold collect; simp only [Pi.add_apply]; abel
    map_smul':=by
       intro a b; funext i; simp only [fullG, Pi.smul_apply,Pi.sub_apply]
       have hp(x:Walk):linkSum (collect G (a • b)) o x=a • linkSum (collect G b) o x:=by
         induction x generalizing o with
         | nil=>simp [linkSum]
         | cons i w hx=>rcases i with ⟨i,h⟩; cases h <;> simp [linkSum,ask,collect,Step.vec,hx,smul_add] -- tune
       simp_rw [Font.pure,sap,hp]; simp only [collect, smul_sub,Pi.smul_apply,RingHom.id_apply] }
lemma top_p(h:Atom f o r)(hs:ContDiffAt ℝ m (satX f) 0)(hp:cFoot m (satX f))(u:Fin m→ InputZ G n): cake m (satX f) u=cake m (satX f) (fullG o ∘ u):=by
 let L:=cake m (satX f); let p:=L.compContinuousLinearMap fun _=> hot G o
 have he:Tensor.Sym p:= fun a s=>top_sym hs (fullG o ∘ a) s
 exact DFunLike.congr_fun (Tensor.ext_diag _ p (top_sym hs) he (funext fun x=> (atop_norm h hs hp x).symm)) u
-- sparse stencil condition on cable
private def nip(G:Gauge)(o:Site n)(r:ℕ): InputZ G n→L[ℝ]InputZ G n:= LinearMap.toContinuousLinearMap
   { toFun:=fun a i=> if separation o i.1 ≤ r then a i else 0, map_add':=by intro a b; funext i; simp only [Pi.add_apply]; split <;> simp_all
     map_smul':=by intro a b; funext i; simp only [Pi.smul_apply,RingHom.id_apply]; split <;> simp_all }
lemma cuts_h(h:Atom f o r)(p:InputZ G n): satX f (nip G o r p)=satX f p:= h.reads _ _ (fun i hi=>by simp only [Work.F03.represent_link]; change G.lieExp (if separation o i.1 ≤ r then _ else _)=_; rw [if_pos hi])
lemma spelt(h:Atom f o r)(hs:ContDiffAt ℝ m (satX f) 0){u:Fin m→ Blip n}(i:Fin m)(hi:r < separation o (u i).1): timeA (cake m (satX f)) u=0:=by
 let P:= satX f; let L:= nip G o r; have hh : ContDiffAt ℝ m P (L 0):= by rw [map_zero]; exact hs
 have he: iteratedFDeriv ℝ m P 0=(iteratedFDeriv ℝ m P 0).compContinuousLinearMap fun _=> L:= calc
    _=iteratedFDeriv ℝ m (P ∘ L) 0:=congr_arg (fun f=> iteratedFDeriv ℝ m f 0) (funext fun v=> (cuts_h h v).symm)
    _=_:=by rw [Push.Uniform.iter_lin_at hh,map_zero]
 ext1 v; change (((m.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ m P 0) _ = 0; rw [_root_.smul_apply,he,ContinuousMultilinearMap.compContinuousLinearMap_apply]
 rw [ContinuousMultilinearMap.map_coord_zero (iteratedFDeriv ℝ m P 0) i,smul_zero]; funext j
 change (if separation o j.1 ≤ r then Pi.single (M:=fun _=> G.Color) (Trot n (u i)) (v i) j else 0)=0
 rw [Pi.single_apply]; split <;> rename_i hp
 · rw [if_neg (by intro hj; subst hj; exact hi.not_ge hp)]
 rfl
end YM.CF.Rel
