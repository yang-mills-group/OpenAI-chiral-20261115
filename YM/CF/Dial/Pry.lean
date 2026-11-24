import YM.CF.Dial.Cheek
/-! Pair-fee acts on a cylinder bundle of a common gauge and two Stun fields. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G: Ratio N P)
lemma spinD : Continuous (brand) := (matter_cont).prodMk SU.fund_cont
lemma profile_c : Continuous (profile (N:=N)) := by
  apply continuous_pi; intro i; apply continuous_pi; intro h; cases h
  · exact (spinD.comp (show Continuous (fun x:Bkg N=> x i) from continuous_apply _)).star
  exact spinD.comp (show Continuous (fun x:Bkg N=> x i) from continuous_apply _)
lemma palt_c:Continuous (palt (N:=N)):= by
  apply continuous_pi; intro i; apply continuous_pi; intro u; have he: Continuous (fun x:Stun N=>localPair (hook x i)):=localPair_cont.comp (continuous_subtype_val.comp (show Continuous (fun x:Stun N=>x i) from continuous_apply _)); cases u
  · exact he.star
  exact he
lemma post_c :Continuous (post (N:=N) (P:=P)) :=by
  apply Continuous.prodMk (f:=fun x: Sew N P=> unionP x.1) _ ((palt_c.comp (continuous_fst.comp continuous_snd)).prodMk (palt_c.comp (continuous_snd.comp continuous_snd)))
  exact (profile_c.comp (continuous_fst.comp continuous_fst)).prodMk (profile_c.comp (continuous_snd.comp continuous_fst))
lemma receipt_c {A: Bale N P→Op (Iota G)}{u:AxisT}{e a p} -- fix
    (h:Crown (badge _) (rope G u e) (rope G u e) a p (fun i=>A i.val)) (hp:0<e): ContinuousOn (fun x:Sew N P=> A (post x)) {x|Gild G x e} :=by
  have hf:Continuous (fun x:TopK G e=> A x.val):=by obtain ⟨F,C,h,w,T⟩:=h; simp_rw [T]; exact continuous_finsetSum _ fun i _=>(h i).toTicket.cont
  exact (continuousOn_iff_continuous_restrict.mpr hf).comp post_c.continuousOn (fun _ p=> ⟨_,p,by simpa⟩)
lemma receipt_i {A:Bale N P→Op (Iota G)}{u:AxisT}{e a p} (h:Crown (badge _) (rope G u e) (rope G u e) a p (fun i=>A i.val))(hp:0<e)(x:Sew N P)(l:Gild G x e)(g):
 (A (post (frost G g x))).trace=(A (post x)).trace:=by
  let f:=h.lib.tiesK.frame g (⟨post x,(show post x∈zoneP G e from ⟨_,l,by simpa⟩)⟩ : TopK G e)
  let S:=(rope G u e).run g; rw [←speak]; exact (congrArg Matrix.trace (show A _=twist S (A (post x)) from f)).trans (trace_twist ..)
variable {j m t:ℕ}{e K a:ℝ}(p:blendS j m e K a t)(h:0<e)(ht:t≤N.val)
include p h ht
def bothV (g : Site (More N)→E)(U:Bkg (More N))(x y:Stun N): Sew N N:= couple (gauge g U) (feast g x) (feast g y)
lemma gazeG (g: Site (More N)→E)(U:Bkg (More N))(x y:Stun N): bothV g U x y=frost (idrat N) g (couple U x y):=by
  have he: scaleG (idrat N) g=g:=by funext i; simp [scaleG, filed]
  simp [bothV,frost,couple,july,he]
lemma step_g (g:Site (More N)→E)(U:Bkg (More N))(x y:Stun N)(hv:Gaze U x y e)(M:Male):
 openC j m M (gauge g U) (feast g x) (feast g y)=openC j m M U x y:=by
  let F:Bale N N → Op (Iota (idrat N)):= earnings (repeated j) (repeated j) m M (idrat N)
  change Matrix.trace (F (post (bothV g U x y)))=Matrix.trace (F (post (couple U x y))); rw [gazeG p h ht]; exact receipt_i _ (A:=F) (p M (idrat N) rfl ht) h _ (hv.glimp _ _ _ h) g
abbrev Gaz (N:Side):= Bkg (More N) × Stun N × Stun N
lemma pore_c(M:Male): ContinuousOn (fun t:Gaz N=> openC j m M t.1 t.2.1 t.2.2) {x:Gaz N|Gaze x.1 x.2.1 x.2.2 e}:=by
  let A:=fun x:Bale N N=> earnings (repeated j) (repeated j) m M (idrat N) x; let f(t:Gaz N): Sew N N:=couple t.1 t.2.1 t.2.2
  have hf: Continuous f:=by unfold f couple; fun_prop
  have hX : ContinuousOn (fun x:Sew N N=> A (post x)) {x| Gild (idrat N) x e}:=receipt_c _ (A:=A) (p M (idrat N) rfl ht) h
  have hs:= hX.comp hf.continuousOn (s:={x|Gaze x.1 x.2.1 x.2.2 e}) (by intro i p; exact Gaze.glimp _ _ _ p h) -- tune set name
  exact continuous_id.matrix_trace.comp_continuousOn hs
end YM.CF.Dial
