import YM.CF.Rel.Atom
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
open Jet
-- actual turns. local norm multilinear by factors
def tools (i m:ℕ)(K:ℝ):ℝ:= (2^i*K)^m
lemma tools_j {H E E':Type}[NormedAddCommGroup E'][NormedSpace ℝ E'][NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup H][NormedSpace ℝ H]{x:E} (m i:ℕ)(f:ContinuousMultilinearMap ℝ (fun _:Fin m=>H) E')(c:Fin m→ E →H)(h:∀ j, Allows i (c j) x C)(hc:0 ≤ C): Allows i (fun y=> f fun j=>c j y) x (‖f‖*tools i m C):=by -- output E' separate induction changes when applying after f curry. can via curryRight f induction E'=(H→L E)...
 induction m generalizing H E' with
 | zero=>
    apply (allows_const _ (v:= f default) (C:=‖f‖*tools i 0 C) ?_).germ; rotate_left
    · refine (f.le_opNorm _).trans_eq ?_; simp [tools]
    exact Eventually.of_forall fun y=>congr_arg f (Subsingleton.elim ..)
 | succ m ih=>
    have hp:= ih f.curryRight (fun j=>c j.castSucc) (fun j=>h j.castSucc)
    apply ((Newt.appliance hp (h (Fin.last m))).mono (le_of_eq ?_)).germ; swap
    · unfold tools; rw [ContinuousMultilinearMap.curryRight_norm, pow_succ]; ring
    exact Eventually.of_forall fun y=>by simp only [ContinuousMultilinearMap.curryRight_apply]; congr 1; ext j; induction j using Fin.lastCases <;> simp
abbrev drapeX(o:Site n)(p: Body 2 n):= silt (G:=G) o (portV p)
def fans (o:Site n)(P:Disk n m)(z:Delph G m):SpaceX G n:= fun i=> z (fun j=> drapeX o (P j) i)
lemma waysV (x y: Config G n)(w:Walk)(p o:Site n)(ht:separation o p+w.length ≤ l)(he:∀ i:Blip n,separation o i.1≤l→ x i=y i): travel x p w=travel y p w:=by
 induction w generalizing p with
 | nil=> rfl
 | cons i w ih=>
    have hp: separation o (p+i.vec) ≤ separation o p+1:= (separation_triangle _ _ _).trans (Nat.add_le_add_left (small p i) _)
    rw [travel,travel, ih _ (by simp only [List.length_cons] at ht; omega)]; congr 1; cases i with
    | mk i t=> cases t
               · exact he (p,i) (by change separation o p ≤ l; omega)
               exact congr_arg (·⁻¹) (he (p-Lattice.step i,i) (by simp only [Step.vec] at hp; dsimp at *; rw [sub_eq_add_neg]; omega))
abbrev tile(x:ℕ):ℕ:=2*(4*x)+4
lemma fees (G:Gauge)(m j:ℕ):∃ f:ℕ→ℝ,nib f∧∀ (l:ℕ){n:Side}(o:Site n)(P:Disk n m), P∈Pots o l m→∀ z: Delph G m, Trade z→ CakeF (fans o P z) o (tile l) j 1 (‖z‖*f l):=by
 obtain ⟨F,hf,h⟩:=yard G j; let M(l):= tools j m (F l); refine ⟨M,((nib_const _ (show 0 ≤ (2:ℝ)^j by positivity)).mul hf|>.pow m),fun l _ o P hP z hz=> ?_⟩; refine ⟨⟨fun u x=>?_, fun i j he=>?_⟩,fun i hi=>?_⟩
 · unfold fans drapeX; simp_rw [silt_g]; exact hz _ _
 · unfold fans; congr 1; funext t; exact congr_arg G.curvature (waysV i j _ o o (by rw [separation_self,zero_add]; exact hub hP) he)
 apply tools_j m j z (fun t x=> drapeX o (P t) (represent x))
 · intro t; have ht:= h l i hi.le o _ (hub (i:=t) hP); exact ⟨ht.analytic.of_le le_top,ht.norm_le⟩
 obtain ⟨_,_,_,h⟩:=hf; exact (h _).1
lemma fans_p(o:Site n)(P: Disk n m)(z: Delph G m): crystal m (satX (fans o P z)) (fun x=> z (fun i=> sumH G x (P i))):=by
 intro x; have he:Tendsto (fun t:ℝ=> z (fun i=> t⁻¹ • drapeX o (P i) (represent (t • x)))) (𝓝[≠] 0) (𝓝 (z (fun i=> sumH G x (P i)))):=z.contDiff (n:=ω)|>.continuous.tendsto _ |>.comp (f:= fun t:ℝ=> fun i=> t⁻¹ • drapeX o (P i) (represent (t • x))) (by
    refine tendsto_pi_nhds.mpr fun i=>?_ ; obtain ⟨⟨a,b⟩,ha⟩:=(ŧ n).surjective (P i); rw [←ha]; unfold drapeX portV; simp_rw [Equiv.symm_apply_apply]; have hp:=pulled_l o (.inl (a,b)) x; rw [show heat o (collect G x) (.inl (a,b))=_ from fundamental G x a b] at hp; exact hp)
 apply he.congr; intro t; change z (fun i=> (fun _=> t⁻¹) i • _) = (t^m)⁻¹ • z _; rw [z.map_smul_univ (fun _=> t⁻¹),Finset.prod_const, card_univ,Fintype.card_fin,inv_pow]
end YM.CF.Rel
