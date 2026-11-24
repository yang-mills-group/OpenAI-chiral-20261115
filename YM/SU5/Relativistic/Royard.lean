import YM.SU5.Relativistic.Dumont
import YM.SU5.Relativistic.Kinesis
import YM.SU5.Relativistic.FirstFrost
/-! # CP11 quantitative UV-Weyl genealogy (all fixed stencils) at once. Selected.
 Retain hard record CP10. Compare hermitian REAL chars—all centers, normalized. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 480000
set_option maxRecDepth 5000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Papal
open Function Filter MeasureTheory Metric
open Lattice SU Buffered Afterglow Journey Preparation CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Satin Tapestry Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice Tower.SlabMark
open scoped Topology BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel.ScreeV CF.Pannier.Chancel.ScreeV.Chateau Tower.Reconstruction Tower.Reconstruction.FermionSlab Crest.Sleet Crest.Sleet.UpStart
open Pitching.Focus Lifted
open CF.Papyrus.Franc CF.Papyrus.Franc.Meshy Loaves
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→Buffered.Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}(D : Exhibition Y H a b I E L B)
variable (G:Tower.SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (d:Axis) (c:∀ j:Axis,Tower.Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "ψ" f:max=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) f)
private lemma rate_buy (m:ℕ) {T:Finset Cover}{F:Buffered.Family (tent Y H)}(t:InTest (tent Y H) true T false F)(v:ℕ)(e:0<v)(h:Between K d 0 (ruler Λ.block * v) T)(z:ℝ)(p:∀ n:ℕ,∀ᶠ i in atTop,∀ᶠ k in atTop,‖sharp Y H m i k (thicket K d v F n)‖ ≤ Real.exp (z*staveP n)):‖(ψ x) m F‖≤Real.exp z:=by
 let x':= (displacement Y H D.univ_ G.history G.clipped d false (c d) x d (c d))
 let X:Tower.Field Y H m d 0 false:=⟨F,(Tower.purpose_ok ..).2 ⟨⟨T,t,(by rw [area0]; exact fun i u=> (h i u).1)⟩,nofun⟩⟩
 let A:Entry Y H m d false v:=⟨X,T,t,h⟩; rw [show F=(actorLabel Y H m d false A.val).val from rfl, ←selected_here Y H D G d d c x m (actorLabel Y H m d false A.val)]
 refine Staved.razorB Y H D.univ_ m G.history G.clipped d false (c d) x' z A e ?_
 intro n; let f:= thicket K d v F n; have he (t':ℕ):TestFamily K true (thicket K d v F t'):=by
    have hh: TestFamily K true F:= Tower.aux_test t
    have hx: TestFamily K true (tripleWide K d v F):= (reflect_ok K d _ hh).mul (move_ok K d _ hh)
    induction t' with|zero=>exact hx|succ i ih=>exact hx.mul (move_ok K d _ ih)
 have ht:=D.univ_.together m f (he n); apply le_of_tendsto ht.periods.norm; exact (D.univ_.pick.grow_i.tendsto_atTop.eventually (p n)).mono (fun i p=> (show ‖I m f (a i)‖ ≤ Real.exp (z *staveP n) from le_of_tendsto (ht.inner (a i)).norm (D.univ_.pick.grow_k.tendsto_atTop.eventually p)))
variable {S:Finset Cover}{A Z δ:ℝ} (h: Inflation A Λ) (v: FairRoute Λ.P Λ.J Λ.h Λ.N0 Push.SectorMeasure.Chi.canonical) (φ:CF.Papyrus.Franc.postage Λ.K.j Z)(x0:0≤Z)(zH: CF.Papyrus.Franc.charge Z≤ Λ.h) (q:Λ.d ≤ δ)(f:∃ N:ℕ,∀ η>(0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N≤n.val→Winter Λ.K.j δ n γ w η)(mK:∀ᶠ n:ℕ in atTop,∀ N:Side,n≤N.val→∀ M:Tulip.Male, Meshy.Muster Λ.d N M)
variable {U:List Wine} (H1:AreaW false S U)(P':InTest (tent Y H) false S false (dek (tent Y H) U))(H₂:Tower.CovCover (tent Y H) (dek (tent Y H) U))
include h v φ x0 zH q f mK H1 H₂ P' G c
private lemma ratesT (w:S.Nonempty) (ε:ℝ)(e:0<ε):∃ ζ>(0:ℝ),∀ z:ℂ,0<‖z‖→‖z‖≤ζ→∀ᶠ n:ℕ in atTop,∀ f:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ, ‖(1:ℂ)+z*((ψ f) n (dek (tent Y H) U) -tallyW U)‖≤Real.exp (5*(ε*‖z‖)):=by
 obtain ⟨z,hz,p⟩:=vintageW Y H v h w e H1 P' H₂ φ x0 zH q f mK d; refine ⟨z,hz,fun a v z'=>?_⟩; obtain ⟨g0,T,b,r,Q,B',V⟩:=p a v z'; let F':= fiz K a U; let F:= relocate K d g0 F'; let A':= 5*(ε* ‖a‖)
 filter_upwards [V] with i g t'
 have H₀:=rate_buy Y H D G d c t' i (F:=F) Q b r B' A' (fun n=> by rw [mul_comm A']; exact g n)
 let X:=dek K U;let s:= -tallyW U; have hs:InTest K true S false X:=P'.widen; have ha:InTest K true S false (X+s • 1):= hs.add (InTest.one.smul s); have ht:InTest K true S false F':= InTest.one.add (ha.smul a)
 have hQ:= consistency Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) t') S i
 rw [show (ψ t') i F=(ψ t') i F' from elect_slide _ _ _ _ _ _ _ _ (aux_test ht) (2*g0) _] at H₀
 apply H₀.trans'; apply le_of_eq; congr 1; change _=(ψ t') i (1+a • (X+s • 1)); rw [hQ.plus_v 1 _ InTest.one (ha.smul a),hQ.unit,hQ.scale _ ha,hQ.plus_v _ _ hs (InTest.one.smul s), hQ.scale _ InTest.one,hQ.unit]; congr 1; dsimp only [smul_eq_mul,mul_one]; rw [sub_eq_add_neg, mul_one s]
omit h v φ x0 zH q f mK H1 H₂ P' G c
private lemma hip(W x:ℝ)(h:0<W)(t: x*W≤1/2)(p:0<x): Real.exp (x*W) ≤ 1+2*x*W :=by
 let u:=x*W; have he:0<u:=mul_pos p h; have hf:u<1:=lt_of_le_of_lt t (by norm_num); apply (Real.exp_bound_div_one_sub_of_interval he.le hf).trans
 apply (div_le_iff₀ (sub_pos.mpr hf)).mpr; have hp:t=t:=rfl; nlinarith only [mul_le_mul_of_nonneg_right t he.le]
private lemma tiny {x:ℂ}(W t:ℝ)(h:0<W)(q:0<t)
    (A:‖1+(W:ℂ)*x‖ ≤1+2*t*W)(B:‖1+ (-(W:ℂ))*x‖ ≤1+2*t*W)(C: ‖1+ Complex.I *(W:ℂ)*x‖≤1+2*t*W)(D:‖1+ (-Complex.I)*(W:ℂ)*x‖ ≤1+2*t*W): ‖x‖ ≤4*t:=by
 have hv :(0:ℝ)<2*t:=by positivity
 have H(x:ℂ)(g:‖x‖≤ 1+2*t*W): x.re≤ 1+2*t*W:= (Complex.re_le_norm _).trans g
 obtain ⟨ha,hb,hc,hd⟩:= (show _ from And.intro (H _ A) (And.intro (H _ B) (And.intro (H _ C) (H _ D))))
 simp only [Complex.add_re,Complex.mul_re,Complex.one_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,zero_mul, sub_zero,neg_zero,Complex.mul_im,mul_zero,neg_mul,one_mul] at ha hb hc hd
 have he: |x.re|≤2*t:=abs_le.mpr (by constructor <;> nlinarith)
 have hx: |x.im|≤ 2*t:=abs_le.mpr (by constructor <;> nlinarith)
 exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)
include h v φ x0 zH q f mK H1 H₂ P' G c
theorem rindV (ε:ℝ) (p:0<ε): ∀ᶠ n:ℕ in atTop,∀ f:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ, ‖(ψ f) n (dek (tent Y H) U)-tallyW U‖≤ε :=by
 let t:=ε/20; have hp:0<t:=by unfold t; positivity
 let T:=(insert 0 S); have hc:AreaW false T U:=by intro i j; obtain ⟨h,t,q,a⟩:= H1 i j; exact ⟨h,fun X Y p=> t _ _ (fun i x v=> p i (Finset.mem_insert_of_mem x) (Finset.mem_insert_of_mem v)),q,fun i v=>Finset.mem_insert_of_mem (a i v)⟩ -- tune
 obtain ⟨ξ,q',u'⟩:= ratesT Y H D G d c h v φ x0 zH q f mK hc (P'.mono (Finset.subset_insert ..)) H₂ (Finset.insert_nonempty ..) t hp
 let W:=min ξ (1/(10*t)); have Ht:0<W:=lt_min q' (by positivity); let A:ℂ:=↑W
 have hA:‖A‖=W:=by unfold A; rw [Complex.norm_real,Real.norm_of_nonneg Ht.le]
 have hx(Z:ℂ)(p:‖Z‖=W): ∀ᶠ n:ℕ in atTop,∀ f:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ, ‖(1:ℂ)+Z*((ψ f) n (dek (tent Y H) U) -tallyW U)‖≤ 1+2*(5*t)*W:=by
    filter_upwards [u' Z (p.symm ▸ Ht) (p.trans_le (min_le_left ..))] with n u f; apply (u f).trans; rw [p,←mul_assoc]; apply hip W _ Ht _ (by positivity); have hx:= (le_div_iff₀ (show 0<10*t by positivity)).mp (min_le_right ξ (1/(10*t))); linarith -- tune
 filter_upwards [hx A hA,hx (-A) (by rw [norm_neg,hA]),hx (Complex.I*A) (by simp [hA]),hx ((-Complex.I)*A) (by simp [hA])] with n X Y Z Q f'
 apply (tiny W (5*t) Ht (by positivity) (X f') (Y f') (Z f') (Q f')).trans_eq; unfold t; ring
end YM.CF.Py.Rate.LocalLimit.Papal
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.rindV
