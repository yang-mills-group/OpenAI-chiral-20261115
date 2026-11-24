import YM.CF.Thera.Hang
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Thera
open Function Filter NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Spire
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {L A m B:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ} {P: Grasp Y B e}(K:Pearl P)(H:Stamped j L ho Y)(p:0<e)(q:1≤j)
variable (G:Ratio (CSide m B) (CSide A B)) (h:G.count=L)(k:P.roundZ ≤(CSide m B).val)(M:Male)(x:nomA m A B)(g:JointB G x e)
variable (L j ho) in
abbrev desire (C: Op (Iota G)):=bentT (pine j L ho (Thread j) true M G (unionP x)) (wh j L ho true M G (unionP x)) (ticketT (Thread j) true M G (unionP x)) C
variable (L j ho) in
def fruit (C: Op (Iota G)):= summit (patchQ G) (traitP (wh j L ho true M G (unionP x)) (pine j L ho (Thread j) true M G (unionP x)) (ticketT (Thread j) true M G (unionP x)) C)
def OrbT {n:Type*}[DecidableEq n][Fintype n](B P C:Op n) : ℝ:=let A:=B*(1+C)*P; -Real.log ((Matrix.det (A*star A+(1-B))).re)/2
lemma orb_snap {n:Type*}[LinearOrder n][Fintype n](P B C:Op n)(x:Wave n)(p:Sea P x)(y:Wave n)(q:Sea B y)(h:IsStarProjection P)(g:IsStarProjection B)(t:Matrix.trace B=Matrix.trace P): Real.log ‖skyGlow y (1+C) x‖ = -OrbT B P C:=by
 unfold OrbT; dsimp only; rw [←show (↑(‖skyGlow y (1+C) x‖^2):ℂ)=_ from prismK h g t (1+C) x p y q]; simp only [Complex.ofReal_re,Real.log_pow]; push_cast; ring
variable {C: Op (Single (CSide A B))}(hV:TagG (spar j M x.1) C)(u: ‖desire L j ho G M x (foot G C)‖<1)
include p k g h
lemma voice (C:Op (Iota G))(s:TagG (foal j true M G (unionP x)) C)(u:‖desire L j ho G M x C‖<1) : let V:= Thread j; let a:=graft G P x.1 M; let b:=changeM P x.2 (upMale L ho M); let X:= spar j (upMale L ho M) x.2; let K:=fruit L j ho G M x C; let α:= desire L j ho G M x C
 TagG X K ∧ fire V G M (unionP x) (acts (exp (dg C)) a)=Complex.exp (altar G P x M+invoice α) • acts (exp (dg K)) b ∧ ∀ z, inner ℂ (mateK _) (fire V G M (unionP x) z)=inner ℂ (oceanA G) z:=by
  intro V a b X K A
  obtain ⟨t,hx⟩:=cue_from x.2; let Z:=starfish m B x.2 t; let z:=accordL G x Z; have hv:=pose_g P p G h k x g Z (starK P.capY p.le g.cg hx)
  let T:=Y.cap G h (P.needed.trans k) M z hv.glyph
  let B:=wh j L ho true M G (unionP x); let Y:=foal j true M G (unionP x); let W:=ticketT V true M G (unionP x); let J:= ticketT V false M G (unionP x); let L':= pine j L ho V true M G (unionP x); have he : Clad Y B W J L':= court G j L ho _ true M (T.chart true) -- tune
  let O:= traitP B L' W C; let P':=patchQ G; let S:= reefS G true; have hw:=reefS_deck G true
  have hT:B=addS P' S X:=pierce ..; have hl: TagG (addS P' S X) O:=hT ▸ (thrust_tag he s (close_c u) : TagG B O)
  have hz:IsStarProjection X:=T.projN; refine ⟨⟨hoc P' S hw hz hl.1 hl.2,halo P' S hw hz hl.1 hl.2⟩,?_, T.fired⟩ -- balance
  have hp:Sea Y a:= carts_sea (switchG G).symm T.projP (sea_g (P.clock_fine G k) x.1 g.fg _)
  have ht:Sea X b:= sea_g k x.2 g.cg _; have he':= taillight he s P' S hw X hz a b hp ht hT u
  let y:=(sect0 G *chargeA V G M (unionP x))⁻¹; change y • _=_
  rw [show pailL _ _ (effectK W _) = _ from he'] -- tune Vx
  rw [Complex.exp_add, charter G h k x g p M,smul_smul]
  congr 1 -- tune
  change y*(Complex.exp (invoice A) * skyGlow (hoist P' S b) W a)=y*(skyGlow (hoist P' S b) W a)*Complex.exp (invoice A); ring
omit p k g h
private lemma footTag {Q S:Op (Single (CSide A B))}(s:TagG Q S):TagG (foot G Q) (foot G S):=by
 refine ⟨?_,?_⟩<;> rw [←foot_mul]; rw [s.1]; rfl; rw [s.2]
lemma re_port (X Y C: Op (Single (CSide A B))) : OrbT (foot G X) (foot G Y) (foot G C)=OrbT X Y C:=by
 unfold OrbT; dsimp only; rw [←foot_one,←foot_add,←foot_mul,←foot_mul,←foot_sub,←foot_s,←foot_mul,←foot_add]; unfold foot; rw [Matrix.det_submatrix_equiv_self] -- tune
include h p u k g hV
lemma laser (t: Matrix.trace (tickA (CSide A B))=Matrix.trace (spar j M x.1))(hx: skyGlow (oceanA G) (1+foot G C) (graft G P x.1 M) ≠ 0): OrbT (tickA (CSide A B)) (spar j M x.1) C= -(altar G P x M+invoice (desire L j ho G M x (foot G C))).re + OrbT (tickA (CSide m B)) (spar j (upMale L ho M) x.2) (fruit L j ho G M x (foot G C)):=by
 obtain ⟨z,l⟩:= cue_from x.2; let Z:=starfish m B x.2 z; let y:=accordL G x Z; have hv:=pose_g P p G h k x g Z (starK P.capY p.le g.cg l)
 let T:=Y.cap G h (P.needed.trans k) M y hv.glyph
 let P':=foal j true M G (unionP x); let B':=tickA (CSide A B)
 let F:=spar j M x.1; let a:= lobe G true; let D:=changeM P x.1 M; let L':= oceanA G; let Y':=graft G P x.1 M; let w:=upMale L ho M; let H:= tickA (CSide m B); let W:=spar j w x.2; let J:=wh j L ho true M G (unionP x); let Q:=foot G C; let U:=fruit L j ho G M x Q; let Z':= changeM P x.2 w; have hk: P'=foot G F:=rfl; have hr:TagG P' Q:=hk.symm ▸ footTag G hV
 obtain ⟨Hq,w',W'⟩:= voice p G h k M x g Q hr u -- tuner
 let K:=altar G P x M+invoice (desire L j ho G M x Q)
 have he:skyGlow L' (1+Q) Y'= Complex.exp K *skyGlow (mateK _) (1+U) Z':=by unfold skyGlow; rw [←tallied Q hr.nil,show inner ℂ L' _= _ from (W' (acts (exp (dg Q)) Y')).symm,w', tallied (fruit L j ho G M x Q) Hq.nil,inner_smul_right]
 let hX:=T.chart true; have hT:= court _ _ _ _ _ _ _ hX; have hz : trace J=trace P':= hT.lengthT
 have hB:Matrix.trace a=B'.trace:=by rw [show a=foot G B' from lobe_t G]; exact Equiv.sum_comp (switchG G) (fun i=>B' i i)
 have hu : Matrix.trace a=Matrix.trace P':=by rw [hk]; rw [hB,t]; exact (Equiv.sum_comp (switchG G) (fun i=>F i i)).symm
 have ht:B'=tickA _:=rfl
 have heK:H.trace=W.trace:=by
   have h1:a=addS (patchQ G) (reefS G true) H:=whale_plus G
   have h2:J=addS (patchQ G) (reefS G true) W:=pierce ..
   rw [←hz,h1,h2] at hu; unfold addS at hu; simp only [Matrix.trace_add,desk_trace] at hu; exact add_left_cancel hu -- tune
 have hR:= orb_snap P' a Q Y' (carts_sea (switchG G).symm T.projP (sea_g (P.clock_fine G k) x.1 g.fg M)) L' (seaA G) hT.proj (lobe_sq ..) hu
 have hV:= orb_snap W H U Z' (sea_g k x.2 g.cg w) (mateK _) (tickB _) T.projN (carts_p _ (cutM_idp _)) heK
 have ht':skyGlow (mateK _) (1+U) Z'≠0:= right_ne_zero_of_mul (he ▸ hx) -- tune
 rw [he,norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)) (norm_ne_zero_iff.mpr ht'),Complex.norm_exp, Real.log_exp,hV,hk,show a=foot G B' from lobe_t G,show Q=_ from rfl,re_port] at hR -- tune
 change OrbT B' F C= -K.re+ OrbT H W U; linarith
end YM.CF.Thera
