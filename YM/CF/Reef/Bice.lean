import YM.CF.Reef.Bronze
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Reef
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N L B A m:Side}{ho:Odd L.val}{j k:ℕ}{a b d r s u v n X l η e:ℝ}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}
variable {G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{K: Aim (CSide A B)} {M:Male}
variable (H:Hull j L ho a b d e k m A B G T F z Y P){R:RG.PathData group}{q:RG.Clip}
def shineP(T:Pride N):Pride N:=fun i j k=> ((T i j k).re:ℂ)
def ClearP(T:Pride N):Prop:= T=shineP T
lemma pig_g(T:Pride N)(U:Pec.Post N): pigment T (echo U)=pigment T U:=by
 have he(s:Signed): Yg (incX s) (echo U)=echo (Yg (incX s) U):= echo_p U s _
 have ht(s:Orig N)(p:Ok N)(x:Post N):silt s p (echo x)=frolic (silt s p x):=by unfold silt; rw [echo_t,swing]
 unfold pigment lexn zinger Pec.tag; simp_rw [he,ht,frolic.inner_map_map] -- tune
lemma shines(T:Pride N)(U:Pec.Post N):pigment (shineP T) U=((pigment T U).re:ℂ):=by
 let f:ℂ→L[ℝ]ℂ := Complex.ofRealCLM.comp Complex.reCLM
 have he(s:Signed)(x): f (Pec.pays s x)= Pec.pays s (f x):=by cases h:detX s<;> simp [Pec.pays,h,f]
 unfold pigment lexn; change _=f ((_:ℝ) • ∑ i:Signed,Pec.pays i (zinger T _)); rw [map_smul,map_sum]; apply congrArg; refine sum_congr rfl ?_; intro i _; rw [he]; apply congrArg; unfold zinger Pec.tag; simp_rw [map_sum]; simp_rw [map_smul]; rfl
lemma spot (T:Pride N)(h:ClearP T)(V: Post N):star (pigment T (echo V))= pigment T V:=by
 rw [pig_g, show pigment T V=pigment (shineP T) V from congrArg (fun t => pigment t V) h, shines]; exact Complex.conj_ofReal _
lemma proof_c(T:Pride N)(h:Lac T u v): ClearP (shineP T) ∧ Lac (shineP T) u v:=by
 refine ⟨funext fun i=>funext fun k=> funext fun s=>?_,⟨?_,?_,fun i=>?_⟩⟩; simp [shineP]
 · intro i z a b; apply congrArg (fun z:ℂ=> ((z.re):ℂ)); exact h.lead ..
 · intro x p q; have he:= h.code x p q; unfold mom shineP; unfold mom at he; simp_rw [←Complex.ofReal_sum,←Complex.re_sum,he]; simp
 refine le_trans ?_ (h.pay i); unfold cents; refine sum_le_sum fun k _=> sum_le_sum fun j _=>?_ ; refine mul_le_mul_of_nonneg_left ?_ (nick_pos _ (ct_pos ..)|>.le); unfold shineP; rw [Complex.norm_real]; exact Complex.abs_re_le_norm _
include H
lemma duty(Q:Pearl P)(x:CryK F z)(p:Cry K)(h:Aim.toll K r s u v)(R: Neat K.x) (M:Male):let f:=deflate (lush G P M K.den ∘ ears F z); f=ᶠ[𝓝 0] fun x=>star (f (cloak _ x)):=by
 intro f; let V:=lush G P M K.den; let g:= V ∘ ears F z; let U: Vox m B →L[ℝ] Vox m B:= cloak _; have he:g ∘ U=ᶠ[𝓝 0] star g:=by
    filter_upwards [salute H x,H.native.melod e H.hi G,heed H x p h M] with i hi hx hp; change lush _ _ _ _ _=star _; unfold lush; rw [show invoice (coatG L ho j G M K.den (ears F z (U i)))=star _ from hp.2, show ears F z (U i)= _ from hi]
    have he:= chain_sym Q H.stamp H.size_p H.above G H.fromL H.hi (ears F z i) hx M diva true; rw [show detX diva.s=false from det_i] at he; rw [show altar G P _ _ = star _ from he]; unfold g V lush; simp -- tune
 have ht: star (g 0)=g 0:=by have he:=he.self_of_nhds; simpa using he.symm
 filter_upwards [he] with x hx; change g (cloak _ x)=star (g x) at hx; change g x-g 0=star (g _-g 0); rw [hx,star_sub,star_star,ht]
lemma shimmering(Q:Pearl P)(x:CryK F z)(p:Cry K)(h:Aim.toll K r s u v)(M:Male)(I:Pride (CSide A B))(J:Pride (CSide m B))(t:ClearP I) (a:ℝ) (V:ContDiffAt ℝ (↑(2:ℕ)) (deflate (lush G P M K.den ∘ ears F z)) 0)(v:cFoot 3 (myth G F z q R P M K.den I J a))(U:R.Bounds q n X l) :cFoot 3 (myth G F z q R P M K.den I (shineP J) a):=by
 let Fv(X:Pride (CSide m B)):= myth G F z q R P M K.den I X a; let Z:ℂ→L[ℝ]ℂ:=Complex.conjCLE.toContinuousLinearMap; have he: ContDiffAt ℝ (↑(2:ℕ)) (Fv J) 0:= (((pane H.native I |>.of_le le_top).add V).sub ((sane U|>.of_le le_top).const_smul a)).sub ((tuck J).of_le le_top)
 apply avg_c he v (cloak _) Z
 filter_upwards [duty H Q x p h p.1 M, salute H x] with y hy hp; let S:= CSide m B; let W:= V; let V:=represent y; have hr: represent (cloak _ y)=echo V:=repr_c y; have hk : baby F z (cloak _ y)=echo (baby F z y):=by
    rw [show baby F z (cloak _ y)=(stanza G diva (xtra true) _).1 from congrArg Prod.fst hp]; change stir _ _ _ = _; rw [stanza_d]; exact stir_d _
 have hu: star (secondM q R (cloak _ y))=secondM q R y:=by apply (Complex.conj_ofReal _).trans; unfold secondM secondTerm; rw [repr_c]; simp_rw [echo_p,quadratic_c U]
 change _=(2:ℝ)⁻¹ • (myth _ _ _ _ _ _ _ _ _ _ _ _+ star (myth G F z _ _ _ _ _ _ _ _ (cloak _ y)))
 unfold myth; rw [star_sub,star_sub,star_add,← hy,star_smul, hu,hk,spot I t,hr, pig_g, shines, star_trivial]; unfold V; generalize _+deflate _ y-a • secondM q R y=D; generalize pigment J (represent y)=Q; apply Complex.ext<;> norm_num <;> ring
end YM.CF.Reef
