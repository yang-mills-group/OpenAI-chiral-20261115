import YM.CF.Dial.Winter
import YM.CF.Phase.Root
/-! Exact unsquared carry along a path, one comparison fee per segment. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
lemma signs_nz {P A:Op n}(h:IsStarProjection P)(g:Aᵀ= -A)(p:IsUnit (stage P A)): filled P A ≠0:=by
  apply nonemptyFill P A h g; intro x he hx
  have hB:acts (stage P A) x=0:=by nth_rw 1 [←he]; rw [←act_mul,stage_right h, body, act_mul, he,hx]
  rw [←act_one x,←(live p).2,act_mul,hB,map_zero]
lemma nodal {P A C:Op n}(h:IsStarProjection P)(e:body P A=body P C): filled P A=filled P C:=by
  have he(C): filled P C=acts (lineOp P) (pairWave (body P C)):=by
    unfold filled; nth_rw 1 [←quant_line h]; rw [act_mul,pair_cov,body,cc,h.isSelfAdjoint.star_eq]
  rw [he A,he C,e]
def berth (n i:ℕ):ℝ:= i/n
def rockZ (V:ℝ→Op n) (P:Op n) (k m :ℕ):ℂ:= ∑ i∈Finset.range k,spark P (V (berth m i)) (V (berth m (i+1)))
def railZ (m a:ℕ): Set ℝ:= Set.Icc (berth m a) (berth m (a+1))
def Stay (P:Op n) (V:ℝ→Op n) (m:ℕ):Prop:= ∀ a<m,∀ x∈railZ m a, (V x)ᵀ= -V x ∧ IsUnit (stage P (V x)) ∧ ‖relay P (V (berth m a)) (V x)-1‖<1
lemma ber_m(m:ℕ):Monotone (berth m):=fun i j h=>div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
lemma berth0(m:ℕ):berth m 0=0:=by simp [berth]
lemma berthLast(m:ℕ)(p:0<m):berth m m=1:=by simp [berth,p.ne']
lemma railIn(m:ℕ)(a:ℕ)(p:a<m): railZ m a⊆ Set.Icc 0 1:=by
  intro x h; have hx:0<m:=by omega
  exact ⟨le_trans ((berth0 m) ▸ ber_m m (show 0≤a from Nat.zero_le _)) h.1,h.2.trans ((berthLast m hx) ▸ ber_m m p)⟩ -- tune
lemma sparkTrip(P:Op n)(h:IsStarProjection P)(V:ℝ→Op n)(e:ContinuousOn V (Set.Icc 0 1))(m a:ℕ)(hA:a<m)(p:Stay P V m):
 let x:=berth m a; ∀ y∈railZ m a, Complex.exp (spark P (V x) (V y)) • filled P (V x)=filled P (V y):=by
  intro x y hy
  obtain ⟨U,s,hs⟩:=spot_projection P h
  let L(t):= spark P (V x) (V t); let q(t):= stratum U s (V t); let H:=railZ m a
  have hx:x∈H:=⟨le_rfl,ber_m m (Nat.le_add_right a 1)⟩
  have hq := p a hA x hx
  have he:L x=0:=spark_equal h hq.2.1
  have hv:= ContinuousOn.mono e (railIn m a hA)
  have hL : ContinuousOn L H := by
    intro v hV; have hb:=p a hA v hV; let f (ν:ℝ):=(P,V x,V ν)
    exact ContinuousAt.comp_continuousWithinAt (spark_contAt hq.2.1 hb.2.2) (f:=f) (continuousWithinAt_const.prodMk (continuousWithinAt_const.prodMk (hv v hV))) -- tune
  have hf : ContinuousOn q H:= by unfold q stratum; exact continuousOn_const.inner (pairWave_cont.comp_continuousOn hv)
  have hk(y)(p':y∈H): q y≠0:=by
    apply strata_gap; rw [←hs]; obtain ⟨q,h,_⟩:= p a hA y p'; exact signs_nz (by assumption) q h
  let T:=fun i=> Complex.exp (L i) * q x
  have hM(y)(p':y∈H):(T y)^2=(q y)^2:=by
    unfold T; rw [mul_pow]; obtain ⟨l,hp,r⟩:=p a hA y p'; have hh:=hq.2.1
    unfold L q; rw [hs]; rw [hs] at hh r; exact spark_sq _ _ hq.1 l hh r
  have hy : T y=q y:= Phase.stalk isPreconnected_Icc ((Complex.continuous_exp.comp_continuousOn hL).mul continuousOn_const) hf x hx hM hk (by simp [T,he,q]) y hy
  change Complex.exp (L y) • _=_
  rw [hs, Fock.placed,Fock.placed,smul_smul]; exact congrArg (fun i:ℂ=> i • wedge U.val s) hy
lemma invoiceP (P:Op n)(h:IsStarProjection P)(V:ℝ→Op n)(e:ContinuousOn V (Set.Icc 0 1))(m:ℕ)(p:0<m)(hA:Stay P V m):
 Complex.exp (rockZ V P m m) • filled P (V 0)=filled P (V 1):=by
  have he(a:ℕ)(g:a≤m): Complex.exp (rockZ V P a m) • filled P (V 0)=filled P (V (berth m a)) := by
    induction a with
    | zero=>simp [berth,rockZ]
    | succ a ih=>
      rw [rockZ,sum_range_succ,add_comm, Complex.exp_add]
      change (Complex.exp _ * Complex.exp (rockZ V P a m)) • _= _
      rw [mul_smul, ih (by omega)]; exact sparkTrip P h V e m a g hA _ ⟨ber_m m (Nat.le_add_right ..),le_rfl⟩
  rw [he m le_rfl,berthLast m p]
lemma princess [Nonempty n] {P C D N:Op n}{m:ℕ}(e:IsStarProjection P)(hn:P*N=N)(p:Stay P (straightC P C D N) m)(g:0<m):
 Complex.exp (rockZ (straightC P C D N) P m m) • filled P D=filled P (N*C*Nᵀ) :=by
  let X:=straightC P C D N; have hc: Continuous X:=by unfold X straightC; fun_prop
  have hz:= invoiceP P e X hc.continuousOn m g p
  rw [show X 0=D by simp [X,straightC], show X 1=victory P C D N by simp [X,straightC]] at hz
  refine hz.trans (nodal e ?_); unfold victory
  have he (A B:Op n):body P (A+B)=body P A+body P B:=by unfold body; rw [mul_add,add_mul];
  rw [he,outsideT e,add_zero]
end YM.CF.Dial
