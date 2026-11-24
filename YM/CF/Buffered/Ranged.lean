import YM.CF.Buffered.Settled
/-! L can be HUGE in operator norm. Both row and column have uniform
approximations to the specified tolerance, uniformly in the holonomies,
including exceptional interpolation at this toron.  Output is a single common
operator for all the sites, graph-neighborhood width paid before measuring a
gram array. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Glaze
open YM.CF.Onyx YM.CF.Emu
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera Tenant Branch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{N:Side}{r C:ℝ}
def sculptM (j k:ℕ) : WG Jill.Male := fun i N x=> sculpt (tickA N) (funde j i N x) k
private lemma pose_p : Lively (fun (_:Jill.Male) N (_:Chin N)=>tickA N) := by
 obtain ⟨a,r,e,h,p,v,t,g⟩:=rock_live Aop
 refine ⟨a,r,e,h,p,v,t,fun i N hv=>?_⟩
 suffices hh : (fun (_:Chin N) => tickA N) = rock Aop from by change Solo a r (fun _=> tickA N) e; rw [hh]; exact g () N hv
 funext x; unfold rock; rw [landP N,turnU]
lemma sculptl(j k:ℕ)(p:1≤j) : Lively (sculptM j k) := by
 let P:= pose_p; let F:= funde_s j p
 induction k with
 | zero => exact Lively.zero
 | succ k ih=> exact (((Lively.one.sub P).prod F).prod P).add (ih.prod (P.sub ((P.prod F).prod P)))

variable {n:Type*}[Fintype n][LinearOrder n]
def Billow (e:ℝ)(P:Op n) := ∀ i:n, ‖acts P (basisKet i)‖≤ e ∧ ‖acts (star P) (basisKet i)‖ ≤ e
lemma Billow.add {P Q:Op n}{e y:ℝ}(p:Billow e P) (q:Billow y Q) : Billow (e+y) (P+Q) := by
 intro i; rw [act_add,star_add,act_add]; exact ⟨(norm_add_le ..).trans (add_le_add (p i).1 (q i).1),(norm_add_le ..).trans (add_le_add (p i).2 (q i).2)⟩
lemma outlet (P:Op n)(p:‖P‖≤r) : Billow r P := by
 intro i; haveI : Nonempty n:=⟨i⟩; refine ⟨(Flare.opy ..).trans (by simp [basisKet,p]),(Flare.opy ..).trans (by simp [basisKet,p])⟩

def Ranged (w:ℕ)(F: Op (Single N)) := ∀ i l: Single N, w < separation (node i.1.1) (node l.1.1) → F i l=0
lemma Ranged.star {F:Op (Single N)}{w:ℕ}(p:Ranged w F): Ranged w (star F) := by
 intro i l h; rw [separation_comm] at h; rw [Matrix.star_apply,p l i h]; simp
lemma range_bill (H:1 ≤ j)(p:0 < r)(v:0<C)(e:ℝ)(q:0<e) : ∃ w t:ℕ,∀ {N:Side}, Pad j N → t≤ N.val →∀ {d:Candle}(F:Slide N d) (M:Jill.Male) (A:Stag N→Peb), (∀ x:Slot,FormU (F.u x) j M r C (trackF F A x)) → ∃ P:Op (Single N),Ranged w P ∧ Billow e (Dofu N A-P) := by
 obtain ⟨k,u,K⟩:=spare H p v (e/2) (by positivity)
 obtain ⟨a,c,y,h,g,z,v',L⟩:= sculptl j k H
 have he: Tendsto (fun w:ℕ=> Real.exp (-a/2*w)*c) atTop (𝓝 0) := by simpa using (show Tendsto (fun w:ℕ=>Real.exp (-a/2*w)) atTop (𝓝 0) from Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith))).mul_const c
 obtain ⟨w,Q⟩:=(he.eventually (gt_mem_nhds (show 0<e/2 by positivity))).exists
 refine ⟨w,max u v',fun {N} i l {d} F M A hv=>?_⟩
 let x:Openc (More N) y:=⟨profile (Kea.tax d), Kea.tax d,tax_guard d _ _ z.le,by simpa⟩
 obtain ⟨W,R,T,J,f⟩:= (show Solo a c _ _ from L M N (by omega)).lib
 let B:=sculptM j k M N x.val
 let Y:=lop W w x
 have hl:‖B-Y‖≤ e/2:= ((show ‖B-Y‖≤Real.exp (-a/2*w)*c from (lip_tail W R T J f h.le).boundOp (by positivity) x)).trans (by exact (show _ < _ from Q).le)
 have ht: B=sculpt (tickA N) (Dofu N (field F j M)) k:=by unfold B sculptM x; dsimp; rw [i.2 _ _ _]
 refine ⟨Y, lop_rad W R T x,?_⟩
 have hx:Billow (e/2) (Dofu N A-B):=by rw [ht]; exact K (by omega) F M A hv i.1
 simpa using (show Billow (e/2+e/2) (Dofu N A-Y) from (by convert hx.add (outlet _ hl) using 1; abel))
#print axioms range_bill
end YM.CF.Buffered.Glaze
