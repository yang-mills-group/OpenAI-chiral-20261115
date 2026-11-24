import YM.CF.Buffered.Fluxion

/-! Uniform wind size threshold for toron pairs. THIS quantifier is before the pivot. -/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {B : Side} {R j:ℕ} {r C:ℝ}
abbrev LedgerR (N:Side) (j:ℕ)(v C e:ℝ)(w: Bool)(A:Melody B R) := ∀ {d:Candle} (F:Slide N d) (V:Stag N→ Peb) (M:Jill.Male), (∀ i,FormU (F.u i) j M v C (trackF F V i))→∀ T D K:Op (Single N), Clad (Dofu N (field F j M)) (tickA N) T D K → Dofu N V=laneP (tickA N) T K →
   ‖A.noteL (Kea.tax d) w (Dofu N V) (Tset N) (Tset N)‖≤e
private lemma sold_era (e:ℝ)(w b c:Bool)(l:Fin 2)(t:0<e)(p:1≤j)(u:0<r)(v:0<C) :
 ∀ᶠ R:ℕ in atTop, ∀ᶠ N:Side in atTop, Even N.val → ∀ (A:Melody B R), A.first.slot=l→ A.face=b→ A.first.wave=c→ LedgerR N j r C e w A := by
 let P(R:ℕ)(N:Side) := Even N.val → ∀ A:Melody B R,A.first.slot=l→ A.face=b→ A.first.wave=c→ LedgerR N j r C e w A
 change ∀ᶠ R:ℕ in atTop, ∀ᶠ N:Side in atTop,P R N
 by_contra k
 obtain ⟨S,h,H⟩ : ∃ S:ℕ→ℕ, (∀ i,i<S i)∧∀ i,∃ᶠ N:Side in atTop,¬P (S i) N := by
   have hp(i:ℕ) : ∃ R:ℕ,i<R∧∃ᶠ N:Side in atTop,¬P R N := by
      obtain ⟨R,x,u⟩:= (not_eventually.mp k|>.and_eventually (eventually_gt_atTop i)).exists
      exact ⟨R,u,not_eventually.mp x⟩
   choose S h g using hp; exact ⟨S,h,g⟩
 let y(i:ℕ):ℝ:=S i
 have hy(i:ℕ):0<y i:=by unfold y; exact_mod_cast show 0<S i from Nat.zero_le _|>.trans_lt (h i)
 have hx(i:ℕ):∃ N:Side,y i* Ember.pinch N ≤ (1/2:ℝ)^i∧¬P (S i) N := by
   obtain ⟨k,X⟩:= Glaze.pick_depth ((1/2)^i/y i) (by have he:=hy i; positivity)
   obtain ⟨T,v,g⟩:= ((H i).and_eventually (eventually_ge_atTop (⟨k+1,by omega⟩:Side))).exists
   exact ⟨T,(mul_comm (y i) _).le.trans ((le_div_iff₀ (hy i)).1 (X (by change k+1 ≤ T.val at g; omega))),v⟩
 choose Y f F using hx
 unfold P LedgerR at F; push Not at F
 choose u' A ha hb hw d Q V M L T D K p' z Z using F
 have he:Yard Y (fun i=>(S i:ℝ)):=by
   refine ⟨hy,?_,?_,u'⟩
   · exact tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun v=> (h v).le) tendsto_id)
   apply squeeze_zero (fun i=>mul_nonneg (hy i).le (Ember.pinch_pos _).le) f (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num))
 have hr:= Melody.progression he p u v L A hb hw ha p' z w; rw [tendsto_zero_iff_norm_tendsto_zero] at hr; obtain ⟨i,k⟩:= (hr.eventually (gt_mem_nhds t)).exists; exact not_lt_of_ge (Z i).le k
lemma Melody.atVertex (p:1≤j)(u:0<r)(v:0<C)(e:ℝ)(t:0<e) : ∀ᶠ R:ℕ in atTop,∀ᶠ N:Side in atTop,Even N.val→∀ A:Melody B R,∀ w:Bool, LedgerR N j r C e w A := by
 have he:= eventually_all.mpr (fun w:Bool=>eventually_all.mpr (fun b:Bool=>eventually_all.mpr (fun c:Bool=> eventually_all.mpr (fun l:Fin 2=> sold_era (B:=B) e w b c l t p u v))))
 filter_upwards [he] with R he
 filter_upwards [eventually_all.mpr (fun w=>eventually_all.mpr (fun b=>eventually_all.mpr (fun c=> eventually_all.mpr (fun l=> he w b c l))))] with N he using fun i A w=> he w A.face A.first.wave A.first.slot i A rfl rfl rfl
#print axioms Melody.atVertex
end YM.CF.Buffered.Ballad
