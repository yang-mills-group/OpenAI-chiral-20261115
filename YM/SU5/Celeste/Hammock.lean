import YM.SU5.Lamour.Laurel
/-! # Flat comparisons BEFORE pruning. tools. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N:Side}{j d:ℕ}{M:Tulip.Male}{ε ζ B:ℝ}
section theta
variable {n:Type*}[LinearOrder n][Fintype n][Nonempty n]{Q P A T:Op n}{U: UNI n}{x y z:Wave n}
lemma alley_sc (x y:Wave n) (Z:FC n) (a:ℂ)(p:a≠0): alleyR x (a • y) Z=alleyR x y Z:=by
 change (inner ℂ x _)⁻¹*inner ℂ x (acts Z (a • y))=(inner ℂ x _)⁻¹ * inner ℂ x (acts Z y); rw [map_smul,inner_smul_right,inner_smul_right,mul_inv_rev]; rw [mul_assoc,inv_mul_cancel_left₀ p]
lemma alley_match (p:IsStarProjection P)(u:Sea P x)(v:Sea P y)(g:FC n): alleyR z x g=alleyR z y g:=by
  let c:= inner ℂ y x; have hx:x=c • y:= u.1.symm.trans (v.scalar p x); have ht:c≠0:=by intro y; have h:=u.2; rw [hx,y,zero_smul,norm_zero] at h; exact zero_ne_one h
  rw [hx,alley_sc _ _ _ _ ht]
variable {S:Finset n}(q:Sea (cutM S) x)(v:Seat N)
local notation "𝓞" => arum U false true x
include q
lemma arum_dot (t:twist U (cutM S)=1-cutM S)(F:FC n): alleyR x (𝓞 y) (theta U F) = star (alleyR x y F):=by
  have he:sings false U (cutM S)=swapX true (cutM S):=t; have hl: tourP U false true F=theta U F:=rfl; rw [←hl]
  change (inner ℂ x _)⁻¹*inner ℂ x (acts (tourP U false true F) (arum U false true x y))=star ((inner ℂ x _)⁻¹*inner ℂ x (acts F y)); let h(w:Wave n): inner ℂ x (arum U false true x w) = star (inner ℂ x w):=by nth_rw 1 [← arum_self U false true S q he]; exact arum_globe U false true S q he _ _
  rw [←arum_act,h,h,star_mul',star_inv₀] -- star_mul'? check
lemma port_sea (t:twist U (cutM S)=1-cutM S)(p:IsStarProjection P)(h:twist U P=1-P)(v:Sea P y): Sea P (𝓞 y):=by
 have hl:sings false U (cutM S)=swapX true (cutM S):= t; refine ⟨?_,(arum_norm U false true S q hl y).trans v.2⟩; nth_rw 1 [←tour_line U false true P P p h]; rw [←arum_act,v.1]
end theta
lemma pane1(N:Side)(i:Axis)(z:ℤ):fling i z N 1=1:=by rw [fling_eq]; unfold Lattice.pull; funext i; unfold Lattice.Step.read; split; exact inv_one; rfl
lemma pane2(N:Side)(i:Axis)(z:ℤ): reflFields i z ((1:Pane N),1)=(1,1) := Prod.ext (pane1 N i z) (pane1 N i z)
variable {F:Mark N}{x y:Wave (Single N)}
local notation "⚝" => spar j M (1:Pane N)
abbrev HaloTw(j:ℕ)(N:Side): Prop:= Kea.Pad j N ∧ ∀ (M:Tulip.Male)(a:Axis)(s:ℤ), twist (carR a s N) (spar j M (1:Pane N))=1-spar j M (1:Pane N)
lemma ownsHalo(p:1≤ j):∀ᶠ N:Side in atTop,Even N.val→HaloTw j N:=by
 obtain ⟨e,h⟩:=flatAcross j p; obtain ⟨a,g⟩:=Kea.gave j p;
 filter_upwards [eventually_ge_atTop (⟨a+e+1,by omega⟩: Side)] with N t z; change a+e+1 ≤ N.val at t; exact ⟨g _ z (by omega),fun M i w=> h _ (by omega) _ i w false⟩
lemma spar_fit(g:Kea.Pad j N): IsStarProjection (⚝):= (coasting g M) ▸ Kea.idol (Kea.too N) j M g.1
lemma mirror_fare (i:Axis)(s:ℤ)(u:HaloTw j N)(p:Sea (⚝) x)(q:Sea (⚝) y)(F : Mark N): alleyR (mateK N) x (reflMark i s F (1,1))=star (alleyR (mateK N) y (F (1,1))):=by
 let U:=carR i s N; let V:= arum U false true (mateK N) y; let k:=spar_fit (M:=M) u.1; have hv:Sea (⚝) V:=port_sea (tick_cut N) (flatTset i s) k (u.2 ..) q
 unfold reflMark; rw [pane2,alley_match k p hv]; exact arum_dot (tick_cut N) (flatTset i s) (F (1,1))
open Next.Rank.Thirst
variable {S:Finset (Seat N)}{o:Seat N}
abbrev BoxProof (ζ C:ℝ)(p:ℝ)(F:Mark N)(S:Finset (Seat N)):Prop:= (∀ X:Fields N,‖F X‖≤C) ∧ ∀ X:Fields N, Rightful S X.1 1 ζ → Rightful S X.2 1 ζ → ‖F X-F (1,1)‖≤p
lemma turnBox {C:ℝ}(p:BoxProof ζ C ε F S) (i:Axis)(s:ℤ): BoxProof ζ C ε (reflMark i s F) (hyphen i s S):=by
 constructor; · intro X; unfold reflMark theta; rw [twist_norm,norm_cc]; exact p.1 _
 intro X u v; unfold reflMark; rw [pane2,←theta_sub,theta,twist_norm,norm_cc]; exact p.2 (reflFields i s X) (Rightful.land u) (Rightful.land v)
lemma turnBlocks (i:Axis)(s:ℤ)(o: Seat N): hyphen i s (BlockP d o)=BlockP d ((plane i s).anon N o):=by
 change hyphen i s (Lattice.halo d {o})= _; rw [coal_halo]; congr 1 
end YM.CF.Lamour.Bridge.Celeste
#print axioms YM.CF.Lamour.Bridge.Celeste.mirror_fare
