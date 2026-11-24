import YM.CF.Tulip.Switch
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir WilsonFrame
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N: Side}
def lawInc (i:Axis)(x:Chin N):= 1-(1/2:ℝ) • (trackM i x+pale (trackM i) x)+rock (gammaOp i) x*((1/2:ℝ) • (trackM i x-pale (trackM i) x))
def dome (N:Side)(x:Chin N):= rock grading x*((-1: Op (Single N))+∑ i,lawInc i x)
lemma dome_bill : Lively (fun (_:Unit) N=> dome N) :=by
  apply Lively.prod (f:=fun _ _ x=>rock grading x) (rock_live grading)
  have hh: Lively (fun (_:Unit) (N:Side) (_:Chin N)=> -(1:Op (Single N))):=by simpa using Lively.one.weighted (ι:=Unit) (-1)
  apply hh.add
  apply allsum; intro i _
  let f:WG Unit:=fun _ _=> trackM i
  have ht: Lively f := allsum _ _ (fun i _=>step_live _ i)
  exact (Lively.one.sub ((ht.add ht.reverseL).scaleR _)).add ((rock_live (gammaOp _)).prod ((ht.sub ht.reverseL).scaleR _))
lemma love_scale (k:ℝ)(A:Op (Model N)): love N (k • A)=k • love N A:=rfl
lemma dome_kernel (U:Bkg (More N)): dome N (profile U)= love N ((frame matter (links U) (anticut N)).H) :=by
  let F:=frame matter (links U) (anticut N)
  have hx(i):lawInc i (profile U)=love N (F.inc i) :=by rw [lawInc,pale,ice_pr,step_profile, inc,lap,diff]; simp only [map_add,map_sub,map_one,map_mul,map_star,love_scale]; rfl
  unfold dome; simp only [hx]; rw [WilsonFrame.H,H0]; simp only [map_mul,map_sum,map_add,map_neg,map_one]; rfl
lemma Broad {e} (p:0<e) (h:256*e≤1/60)(U:Bkg (More N))(hU: Cube.Guard U e): Safe (dome N (profile U)) :=by
  rw [dome_kernel]; exact pushed (band matter _ _ ( (Cube.Guard.shrink (Cube.Guard.children hU p.le) h).2))
lemma calm : ∃ (r e:ℝ),0<r∧ r<1 ∧ 0<e∧∃ v:ℕ,∀ (N:Side),v≤N.val →∀ x∈ Openc (More N) e, ‖slack (dome N x)‖≤r :=by
  let K:WG Unit:=fun _ N x=> slack (dome N x); have he:Lively K:=by unfold K slack; simp only [sq]; exact Lively.one.sub ((dome_bill.prod dome_bill).scaleR _)
  obtain ⟨a,c,d,hp,hc,hd,v,G⟩:=he
  obtain ⟨y,hy,H⟩:=exists_between rho_lt
  let δ:=min d (min ((1/60:ℝ)/256) ((y-rho)/(c*(4/a))*d)); have ht: 0 < c*(4/a):=by positivity
  have hδ:0<δ:=by unfold δ; exact lt_min hd (lt_min (by norm_num) (mul_pos (div_pos (sub_pos.mpr hy) ht) hd))
  have hh': δ≤d:=min_le_left ..; have hf:δ≤(1/60:ℝ)/256:=(min_le_right ..).trans (min_le_left ..); have hh:δ≤((y-rho)/(c*(4/a))*d):=(min_le_right ..).trans (min_le_right ..)
  refine ⟨y,δ, rho_pos.trans hy,H,hδ,v,fun N hv x hx=>?_⟩
  obtain ⟨U,hU,hu⟩:=hx
  let Y:=profile U
  have he: Safe (dome N Y):= Broad hδ (by linarith) U hU
  have hyi:Y∈Openc (More N) d:= ⟨U,hU.shrink hh', by simpa [Y]⟩; have hx': x∈Openc (More N) d:=⟨U,hU.shrink hh',lt_of_lt_of_le hu hh'⟩
  have hk:‖slack (dome N x) - slack (dome N Y)‖≤y-rho := le_trans (landscape (G () N hv) hp hd x Y hx' hyi) (by
      change c*(4/a)*(‖x-Y‖/d)≤_
      have hr: ‖x-Y‖/d ≤(y-rho)/(c*(4/a)) :=(div_le_iff₀ hd).mpr (hu.le.trans hh)
      exact (mul_le_mul_of_nonneg_left hr ht.le).trans_eq (by field_simp))
  exact (norm_le_norm_sub_add _ (slack (dome N Y))).trans ((add_le_add hk he.good).trans_eq (sub_add_cancel ..))
lemma oriented_love {A:Op (Model N)}(h:Safe A): projector (love N A)=love N (projector A):=by
  have hh := (rs_sum (h.good.trans_lt rho_lt)).map (love N).toRingEquiv.toAddMonoidHom ((StarAlgEquiv.isometry (love N)).continuous)
  have he (i): love N (rsTerm A i) = rsTerm (love N A) i := by simp only [rsTerm,slack,map_pow, map_sub,map_one,love_scale]
  have hp: rsEval (love N A)=love N (rsEval A):=by
    apply HasSum.unique (rs_sum ((pushed h).good.trans_lt rho_lt))
    rw [show rsTerm (love N A)=(fun i=> love N (rsTerm A i)) from funext fun i=> (he i).symm]; exact hh
  simp only [projector,polarity,map_add,map_mul,map_one,love_scale,hp]
variable {ι:Type*}{f:WG ι}
lemma royal (h:Lively f){r e v}(he:0<e)(hp:0<r)(hr:r<1)(p:∀ i N,v≤ N.val →∀ x∈Openc (More N) e, ‖slack (f i N x)‖ ≤ r) : Lively (fun i N x=> projector (f i N x)):=by
  have hs:Lively (fun i N x=> slack (f i N x)):=by unfold slack; simp only [sq]; exact Lively.one.sub ((h.prod h).scaleR _)
  obtain ⟨a,k,M,d,ha,hk,hk',hM,hd,l,H⟩:= hs.rotor r hp hr he p
  let V(m:ℕ):=M*k^m; have hV: Summable V:= (summable_geometric_of_lt_one hk.le hk').mul_left _
  have hh:Lively (fun i N x=> rsEval (f i N x)):=by
    refine certify ha hd (v:=l) (r:=∑' n,V n) (fun i N hv=>?_)
    have hx (n) : Crown (badge _) (bail N d) (bail N d) a (V n) (fun x=> rsTerm (f i N x.val) n) :=by
      have Hx:= (H n i N hv).scale ((SignScalar.c n:ℝ):ℂ)
      simp only [Complex.norm_real] at Hx
      have hm:=Hx.books (show ‖SignScalar.c n‖*(M*k^n)≤V n from (by unfold V; exact mul_le_of_le_one_left (by positivity) (SignScalar.c_norm _)))
      convert hm using 1; ext1 x; exact RCLike.real_smul_eq_coe_smul ..
    -- topology equality via entries
    have Hw:= Crown.tsK V hx ha.le hV
    convert Hw using 1; rfl
  exact (Lively.one.add ((h.scaleR _).prod hh)).scaleR _
lemma dome_cap: Lively fun (_:Unit) N x=> projector (dome N x):=by obtain ⟨r,e,h,g,p,v,Q⟩:=calm; exact royal dome_bill p h g fun _=>Q
end YM.CF.Tulip
