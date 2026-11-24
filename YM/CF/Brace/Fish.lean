import YM.CF.Brace.Quartz
/-! Gauge covariance, continuity port for general history. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B N : Side}{j:ℕ}
structure Sparkle (N:Side)(e:ℝ)(M:Tulip.Male)(j:ℕ): Prop where
  continuousOn : ContinuousOn (spar j M (N:=N)) {U|Guard U e}
  covary (U:Bkg (More N))(g:Site (More N)→E)(h:Guard U e): spar j M (gauge g U)=twist (tradew N g) (spar j M U)
  projection (U:Bkg (More N))(h:Guard U e) : IsStarProjection (spar j M U)
lemma drift_l(j:ℕ)(h:1≤j): ∃ e:ℝ,0<e ∧ ∃ n:ℕ,∀ N':Side,n≤N'.val→∀ (M:Tulip.Male), Sparkle N' e M j:=by
 obtain ⟨a,c,e,hp,hc,hE,v,F⟩:=funde_s j h; obtain ⟨b,p,w,H⟩:= funde_q j h
 let d:=min b e; have hd:0<d:=lt_min p hE
 refine ⟨d,hd,max v w,fun N he M=>?_⟩
 have f:=axis_down a c (F M N ((le_max_left ..).trans he)) _ hd (min_le_right b e)
 have hh: ∀ U,Guard U d → profile U∈Openc (More N) d := fun U h=> ⟨U,h,by simpa using hd⟩
 let k:= funde j M N
 refine ⟨?_,fun U g h=>?_, fun U h=> H M N ((le_max_right ..).trans he) U (h.shrink (min_le_left ..))⟩
 · have he:Continuous (fun x:Openc (More N) d=>k x.val):=by obtain ⟨G,C,h,V,H⟩:=f; simp_rw [k,H]; exact continuous_finsetSum _ fun i _=>(h i).toTicket.cont -- tune dsimp
   exact (continuousOn_iff_continuous_restrict.mpr he).comp profile_c.continuousOn (fun i h=> hh i h) -- hh arrow shape
 unfold spar; rw [profile_g]; exact f.lib.tiesK.frame g (⟨profile U,hh U h⟩ : Openc (More N) d)
lemma Sparkle.red {a b:ℝ}{M:Tulip.Male}(h:Sparkle N a M j)(p:b≤a): Sparkle N b M j:=by
 refine ⟨h.continuousOn.mono (fun U g=>Cube.Guard.shrink g p),fun U t g=>h.covary U t (g.shrink p),fun U g=>h.projection U (g.shrink p)⟩ -- Implicit function type
lemma post_glow(X:Stun N)(g:Site (More N)→E):postC (feast g X)=congrC (tradew N g) (postC X):=by
 let T:=g∘node; let A:=conjG matter T; let V:=spotC (N:=N); let f(i:Site N):=hook X (node i);
 unfold postC spotC; rw [show hook (feast g X)∘node=(fun i=> turn (T i) (f i)) from rfl, C_gauge];
 have he: portW (helix N).symm A.val=(tradew N g).val:=by
   unfold portW A; ext ⟨⟨i,b⟩,v⟩ ⟨⟨j,c⟩,k⟩; by_cases h:i=j<;>by_cases e:b=c<;> simp [h,e,conjG,tradew,jump_apply, helix, Lat.color] <;> first| rfl|simp
 let Q:=helix N; rw [congrC,← he]; unfold portW; simp only [Equiv.symm_symm]; rw [show (A.val.submatrix Q Q)ᵀ=A.valᵀ.submatrix Q Q from rfl,Matrix.submatrix_mul_equiv A.val _ _ Q _, Matrix.submatrix_mul_equiv _ _ _ Q _]; rfl
variable {F:Duet m B}{e p:ℝ}{M:Tulip.Male}(g:enoughV B e p)(he:0≤e)(h:Cane (CSide m B) j M e p F)
include g he h
lemma phase_g(U:Skin m B)(p':Guard U e)(x: Sheen m B)(hx: Slow U (hook x) p) (t:Site (Domain m B)→E)(k:Sparkle (CSide m B) e M j): chant m B j M F (gauge t U)=effectK (tradew _ t).val (chant m B j M F U):=by
 let Z:=feast t x; have hh:Slow (gauge t U) (hook Z) p:=slow_g _ _ t hx
 let T:=tradew _ t
 rw [calm g he h _ (p'.cov t) Z hh, calm g he h _ p' x hx,rootsD,song_g g he h _ p' x hx]; unfold Z coneP; rw [post_glow,k.covary _ t p',filled_twist, rootsD];
 let v:= Complex.exp (-song m B F U x) • coneP j M U x
 change sized (_ • acts (quantU T).val _) = acts (quantU T).val (sized v)
 rw [←map_smul,sized, sized,act_unit_norm]; change (↑‖v‖:ℂ)⁻¹ • _= _;  exact (map_smul (acts (quantU T).val) _ v).symm
end YM.CF.Brace
