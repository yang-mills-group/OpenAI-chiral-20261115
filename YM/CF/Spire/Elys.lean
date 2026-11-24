import YM.CF.Spire.Sum
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {L m A B : Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e:ℝ} {P: Grasp Y B e}
variable (K:Pearl P)(w:Stamped j L o Y)(k:P.roundZ≤ (CSide m B).val)(p:1≤j)
lemma candleN (M:Tulip.Male)(U:Skin m B): (candle m B (P.cost m M) U).re=0:=by simp [candle,zen]
def changeM (P: Grasp Y B e)(U:Skin m B)(M:Tulip.Male): Wave (Single (CSide m B)):= Complex.exp (-candle m B (P.cost m M) U) • chant m B j M (P.cost m M) U
include p K w k
lemma change_v (M:Tulip.Male)(x:Skin m B)(g:Guard x e)(X:Stun (CSide m B))(t:Slow x (hook X) K.q) (u:ℝ)(e:Real.exp u= ‖coneP j M x X‖): Complex.exp ((u:ℂ) + zen (hum m B (P.cost m M) x X)) • changeM P x M=coneP j M x X:=by
 unfold changeM; rw [smul_smul,←Complex.exp_add,candleL K w k p x g M X t,zen_a, show (u:ℂ) + zen (hum m B (P.cost m M) x X)+ -(zen (hum m B (P.cost m M) x X)-zen (song m B (P.cost m M) x X))=(u:ℂ)+zen (song m B (P.cost m M) x X) by abel]; exact (phaseLift P.topB P.baseY.1 (P.couture k M) x g X (fun i j=>(t i j).trans_le (K.roof.trans P.small)) u e.symm).symm
omit p K k w
lemma ley (a:ℝ)(z:ℂ)(b:Bool): cSignX b ((a:ℂ)+zen z)=(a:ℂ)+zen (cSignX b z):=by cases b; rfl; simp [cSignX,zen] -- tune
lemma humanity(m B :Side)(F :Duet m B)(U:Skin m B)(X:Stun (CSide m B))(a:Shape)(b:Bool): hum m B F (stir (xtra b) a U) (fume (xtra b) a X)=cSignX (b.xor (detX a.s)) (hum m B F U X):=by
 let S:= Sweep.mk a.s (wrap (CSide m B) a.t) b; rw [show stir (xtra b) a U=flashA S U from (stir_e a b U).symm,show fume (xtra b) a X=fireA S X from (fume_e ..).symm]; exact song_x _ _ F U X S
lemma mark_ext {Z: Type*}[NormedAddCommGroup Z][NormedSpace ℂ Z]{x y:Z}{c:ℂ}(h:c≠0)(p:c • x=c • y):x=y:=by rw [← inv_smul_smul₀ h x, p,inv_smul_smul₀ h]
include p K w k
lemma chapelN (x:Stun (CSide m B))(g:Skin m B)(u:Guard g e)(M:Tulip.Male)(a:Shape){b r:Bool}(T:ColorT b)(S:UNI SpinIdx)(t: JetS a.s b r S): ‖coneP j M (stir T a g) (fume T a x)‖=‖coneP j M g x‖:=by rw [←arum_post a T S t p g (w.fields_one _ (P.needed.trans k)) (u.shrink P.gem) x]; exact arum_norm _ _ _ (Tset _) (touchP _ ▸ tickB (CSide m B)) (tickR a T S t _) _ -- tune
lemma change_g (x:Skin m B)(g:Guard x e)(M:Tulip.Male)(a:Shape)(b: Bool){r:Bool}(S:UNI SpinIdx)(t: JetS a.s b r S): arum (prepU a S (xtra b) (CSide m B)) b r (mateK _) (changeM P x M)=changeM P (stir (xtra b) a x) M:=by
 let N:=CSide m B; let f:=P.cost m M
 let X:=starfish m B x (cue_from x).choose; have hx:Slow x (hook X) K.q:=fun i j=>(starK K.ample P.baseY.1 g (cue_from x).choose_spec i j).trans_le K.wide
 let u:= Real.log ‖coneP j M x X‖; have he:Real.exp u= ‖coneP j M x X‖:=by
   have hp:Slow x (hook X) P.p:=fun i j=>(hx i j).trans_le (K.roof.trans P.small); exact Real.exp_log (norm_pos_iff.mpr (((P.couture k M).rhythm x g X hp X hp).2))
 let Z:= xtra b; let Y:=fume Z a X; let V:=stir Z a x
 have hv:= chapelN K w k p X x g M a Z S t
 have hZ:=change_v K w k p M V (keepC Z a _ e g) Y (swayX _ _ _ X K.q hx) _ (he.trans hv.symm)
 let z:= Complex.exp ((u:ℂ)+zen (hum m B f V Y)); have hz':z=cSignX (b.xor r) (Complex.exp ((u:ℂ)+zen (hum m B f x X))):=by rw [←cSexp,ley]; unfold z V Z Y; rw [humanity,mono_d a.s b r S t] -- tune
 apply mark_ext (c:=z) (Complex.exp_ne_zero _)
 rw [show z • changeM P (stir _ _ _) M= _ from hZ, hz',←arum_scale,change_v K w k p _ _ g X hx u he,arum_post _ _ S t p x (w.fields_one _ (P.needed.trans k)) (g.shrink P.gem) X]
omit p K w
variable (G:Ratio (CSide m B) (CSide A B))(h:G.count=L)
abbrev venture (P:Grasp Y B e)(x:sewA m A B)(M:Tulip.Male):ℂ:= firmL P G x M - trace (eExp (Thread j) Y.k M G (post x))
include h
lemma vale(x:sewA m A B)(g:SectorK P G x)(M:Tulip.Male): Complex.exp (venture G P x M)=(sect0 G*chargeA (Thread j) G M (unionP x.1))⁻¹* skyGlow (sear P G x.1.2 (upMale L o M)) (ticketT (Thread j) true M G (unionP x.1)) (adjust P G x.1.1 M):=by
 let u:=sect0 G; have he :u≠0:=norm_pos_iff.mp ((sectorU G).symm ▸ zero_lt_one); have hx:= hymn P G h k x g M; have hz:= (Y.cap _ h (P.needed.trans k) M _ g.glyph).pay; change chargeA (Thread j) G M (unionP x.1)=_ at hz; rw [hz,← show (post x).1=unionP x.1 from rfl,hx]; unfold venture; rw [Complex.exp_sub]; change _=(u*_)⁻¹*(u*_); field_simp -- tune
lemma vcont(M:Tulip.Male):ContinuousOn (fun x: sewA m A B=>venture G P x M) {x|SectorK P G x}:=by
 have ht:ContinuousOn (fun x:sewA m A B=>trace (eExp (Thread j) Y.k M G (post x))) {x|SectorK P G x}:=continuous_id.matrix_trace.comp_continuousOn ((receipt_c G (A:= eExp (Thread j) Y.k M G) (Y.beauty _ _ h (P.needed.trans k)) Y.range).mono fun i p=> (show SectorK _ _ _ from p).glyph)
 exact (firm_c P G h k M).sub ht
lemma worth (x:nomA m A B)(Z:ℝ→ Stun (CSide A B))(S:Stun (CSide m B))(M:Tulip.Male)(u:ContinuousOn Z (Set.Icc 0 1))(t:∀ i∈Set.Icc (0:ℝ) 1,SectorK P G (x,Z i,S)): venture G P (x,Z 0,S) M=venture G P (x,Z 1,S) M:=by
 let f:=fun i:ℝ=>(x,Z i,S); let v:=fun i:ℝ=> venture G P (f i) M; have hp:(0:ℝ)∈Set.Icc 0 1:=⟨le_rfl,zero_le_one⟩
 have hz:ContinuousOn v (Set.Icc 0 1):=(vcont k G h _).comp (f:=f) (continuousOn_const.prodMk (u.prodMk continuousOn_const)) t
 exact carry_log isPreconnected_Icc (v:=fun _=> v 0) continuousOn_const hz _ hp (fun y p=>(vale k G h _ (t 0 hp) M).trans (vale k G h _ (t y p) M).symm) rfl _ ⟨zero_le_one,le_rfl⟩ -- tune args
end YM.CF.Spire
