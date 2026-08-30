/*******************************************************************
 * This file is part of the Emulex Linux Device Driver for         *
 * Fibre Channel Host Bus Adapters.                                *
 * Copyright (C) 2004-2015 Emulex.  All rights reserved.           *
 * EMULEX and SLI are trademarks of Emulex.                        *
 * www.emulex.com                                                  *
 * Portions Copyright (C) 2004-2005 Christoph Hellwig              *
 *                                                                 *
 * This program is free software; you can redistribute it and/or   *
 * modify it under the terms of version 2 of the GNU General       *
 * Public License as published by the Free Software Foundation.    *
 * This program is distributed in the hope that it will be useful. *
 * ALL EXPRESS OR IMPLIED CONDITIONS, REPRESENTATIONS AND          *
 * WARRANTIES, INCLUDING ANY IMPLIED WARRANTY OF MERCHANTABILITY,  *
 * FITNESS FOR A PARTICULAR PURPOSE, OR NON-INFRINGEMENT, ARE      *
 * DISCLAIMED, EXCEPT TO THE EXTENT THAT SUCH DISCLAIMERS ARE HELD *
 * TO BE LEGALLY INVALID.  See the GNU General Public License for  *
 * more details, a copy of which can be found in the file COPYING  *
 * included with this package.                                     *
 *******************************************************************/

#include <linux/blkdev.h>
#include <linux/delay.h>
#include <linux/dma-mapping.h>
#include <linux/idr.h>
#include <linux/interrupt.h>
#include <linux/module.h>
#include <linux/kthread.h>
#include <linux/pci.h>
#include <linux/spinlock.h>
#include <linux/ctype.h>
#include <linux/aer.h>
#include <linux/slab.h>
#include <linux/firmware.h>
#include <linux/miscdevice.h>
#include <linux/percpu.h>

#include <scsi/scsi.h>
#include <scsi/scsi_device.h>
#include <scsi/scsi_host.h>
#include <scsi/scsi_transport_fc.h>

#include "lpfc_hw4.h"
#include "lpfc_hw.h"
#include "lpfc_sli.h"
#include "lpfc_sli4.h"
#include "lpfc_nl.h"
#include "lpfc_disc.h"
#include "lpfc_scsi.h"
#include "lpfc.h"
#include "lpfc_logmsg.h"
#include "lpfc_crtn.h"
#include "lpfc_vport.h"
#include "lpfc_version.h"

char *_dump_buf_data;
unsigned long _dump_buf_data_order;
char *_dump_buf_dif;
unsigned long _dump_buf_dif_order;
spinlock_t _dump_buf_lock;

/* Used when mapping IRQ vectors in a driver centric manner */
uint16_t *lpfc_used_cpu;
uint32_t lpfc_present_cpu;

static void lpfc_get_hba_model_desc(struct lpfc_hba *, uint8_t *, uint8_t *);
static int lpfc_post_rcv_buf(struct lpfc_hba *);
static int lpfc_sli4_queue_verify(struct lpfc_hba *);
static int lpfc_create_bootstrap_mbox(struct lpfc_hba *);
static int lpfc_setup_endian_order(struct lpfc_hba *);
static void lpfc_destroy_bootstrap_mbox(struct lpfc_hba *);
static void lpfc_free_els_sgl_list(struct lpfc_hba *);
static void lpfc_init_sgl_list(struct lpfc_hba *);
static int lpfc_init_active_sgl_array(struct lpfc_hba *);
static void lpfc_free_active_sgl(struct lpfc_hba *);
static int lpfc_hba_down_post_s3(struct lpfc_hba *phba);
static int lpfc_hba_down_post_s4(struct lpfc_hba *phba);
static int lpfc_sli4_cq_event_pool_create(struct lpfc_hba *);
static void lpfc_sli4_cq_event_pool_destroy(struct lpfc_hba *);
static void lpfc_sli4_cq_event_release_all(struct lpfc_hba *);
static void lpfc_sli4_disable_intr(struct lpfc_hba *);
static uint32_t lpfc_sli4_enable_intr(struct lpfc_hba *, uint32_t);
static void lpfc_sli4_oas_verify(struct lpfc_hba *phba);

static struct scsi_transport_template *lpfc_transport_template = NULL;
static struct scsi_transport_template *lpfc_vport_transport_template = NULL;
static DEFINE_IDR(lpfc_hba_index);

/**
 * lpfc_config_port_prep - Perform lpfc initialization prior to config port
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine will do LPFC initialization prior to issuing the CONFIG_PORT
 * mailbox command. It retrieves the revision information from the HBA and
 * collects the Vital Product Data (VPD) about the HBA for preparing the
 * configuration of the HBA.
 *
 * Return codes:
 *   0 - success.
 *   -ERESTART - requests the SLI layer to reset the HBA and try again.
 *   Any other value - indicates an error.
 **/
int
lpfc_config_port_prep(struct lpfc_hba *phba)
{
	lpfc_vpd_t *vp = &phba->vpd;
	int i = 0, rc;
	LPFC_MBOXQ_t *pmb;
	MAILBOX_t *mb;
	char *lpfc_vpd_data = NULL;
	uint16_t offset = 0;
	static char licensed[56] =
		    "key unlock for use with gnu public licensed code only\0";
	static int init_key = 1;

	pmb = mempool_alloc(phba->mbox_mem_pool, GFP_KERNEL);
	if (!pmb) {
		phba->link_state = LPFC_HBA_ERROR;
		return -ENOMEM;
	}

	mb = &pmb->u.mb;
	phba->link_state = LPFC_INIT_MBX_CMDS;

	if (lpfc_is_LC_HBA(phba->pcidev->device)) {
		if (init_key) {
			uint32_t *ptext = (uint32_t *) licensed;

			for (i = 0; i < 56; i += sizeof (uint32_t), ptext++)
				*ptext = cpu_to_be32(*ptext);
			init_key = 0;
		}

		lpfc_read_nv(phba, pmb);
		memset((char*)mb->un.varRDnvp.rsvd3, 0,
			sizeof (mb->un.varRDnvp.rsvd3));
		memcpy((char*)mb->un.varRDnvp.rsvd3, licensed,
			 sizeof (licensed));

		rc = lpfc_sli_issue_mbox(phba, pmb, MBX_POLL);

		if (rc != MBX_SUCCESS) {
			lpfc_printf_log(phba, KERN_ERR, LOG_MBOX,
					"0324 Config Port initialization "
					"error, mbxCmd x%x READ_NVPARM, "
					"mbxStatus x%x\n",
					mb->mbxCommand, mb->mbxStatus);
			mempool_free(pmb, phba->mbox_mem_pool);
			return -ERESTART;
		}
		memcpy(phba->wwnn, (char *)mb->un.varRDnvp.nodename,
		       sizeof(phba->wwnn));
		memcpy(phba->wwpn, (char *)mb->un.varRDnvp.portname,
		       sizeof(phba->wwpn));
	}

	phba->sli3_options = 0x0;

	/* Setup and issue mailbox READ REV command */
	lpfc_read_rev(phba, pmb);
	rc = lpfc_sli_issue_mbox(phba, pmb, MBX_POLL);
	if (rc != MBX_SUCCESS) {
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0439 Adapter failed to init, mbxCmd x%x "
				"READ_REV, mbxStatus x%x\n",
				mb->mbxCommand, mb->mbxStatus);
		mempool_free( pmb, phba->mbox_mem_pool);
		return -ERESTART;
	}


	/*
	 * The value of rr must be 1 since the driver set the cv field to 1.
	 * This setting requires the FW to set all revision fields.
	 */
	if (mb->un.varRdRev.rr == 0) {
		vp->rev.rBit = 0;
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0440 Adapter failed to init, READ_REV has "
				"missing revision information.\n");
		mempool_free(pmb, phba->mbox_mem_pool);
		return -ERESTART;
	}

	if (phba->sli_rev == 3 && !mb->un.varRdRev.v3rsp) {
		mempool_free(pmb, phba->mbox_mem_pool);
		return -EINVAL;
	}

	/* Save information as VPD data */
	vp->rev.rBit = 1;
	memcpy(&vp->sli3Feat, &mb->un.varRdRev.sli3Feat, sizeof(uint32_t));
	vp->rev.sli1FwRev = mb->un.varRdRev.sli1FwRev;
	memcpy(vp->rev.sli1FwName, (char*) mb->un.varRdRev.sli1FwName, 16);
	vp->rev.sli2FwRev = mb->un.varRdRev.sli2FwRev;
	memcpy(vp->rev.sli2FwName, (char *) mb->un.varRdRev.sli2FwName, 16);
	vp->rev.biuRev = mb->un.varRdRev.biuRev;
	vp->rev.smRev = mb->un.varRdRev.smRev;
	vp->rev.smFwRev = mb->un.varRdRev.un.smFwRev;
	vp->rev.endecRev = mb->un.varRdRev.endecRev;
	vp->rev.fcphHigh = mb->un.varRdRev.fcphHigh;
	vp->rev.fcphLow = mb->un.varRdRev.fcphLow;
	vp->rev.feaLevelHigh = mb->un.varRdRev.feaLevelHigh;
	vp->rev.feaLevelLow = mb->un.varRdRev.feaLevelLow;
	vp->rev.postKernRev = mb->un.varRdRev.postKernRev;
	vp->rev.opFwRev = mb->un.varRdRev.opFwRev;

	/* If the sli feature level is less then 9, we must
	 * tear down all RPIs and VPIs on link down if NPIV
	 * is enabled.
	 */
	if (vp->rev.feaLevelHigh < 9)
		phba->sli3_options |= LPFC_SLI3_VPORT_TEARDOWN;

	if (lpfc_is_LC_HBA(phba->pcidev->device))
		memcpy(phba->RandomData, (char *)&mb->un.varWords[24],
						sizeof (phba->RandomData));

	/* Get adapter VPD information */
	lpfc_vpd_data = kmalloc(DMP_VPD_SIZE, GFP_KERNEL);
	if (!lpfc_vpd_data)
		goto out_free_mbox;
	do {
		lpfc_dump_mem(phba, pmb, offset, DMP_REGION_VPD);
		rc = lpfc_sli_issue_mbox(phba, pmb, MBX_POLL);

		if (rc != MBX_SUCCESS) {
			lpfc_printf_log(phba, KERN_INFO, LOG_INIT,
					"0441 VPD not present on adapter, "
					"mbxCmd x%x DUMP VPD, mbxStatus x%x\n",
					mb->mbxCommand, mb->mbxStatus);
			mb->un.varDmp.word_cnt = 0;
		}
		/* dump mem may return a zero when finished or we got a
		 * mailbox error, either way we are done.
		 */
		if (mb->un.varDmp.word_cnt == 0)
			break;
		if (mb->un.varDmp.word_cnt > DMP_VPD_SIZE - offset)
			mb->un.varDmp.word_cnt = DMP_VPD_SIZE - offset;
		lpfc_sli_pcimem_bcopy(((uint8_t *)mb) + DMP_RSP_OFFSET,
				      lpfc_vpd_data + offset,
				      mb->un.varDmp.word_cnt);
		offset += mb->un.varDmp.word_cnt;
	} while (mb->un.varDmp.word_cnt && offset < DMP_VPD_SIZE);
	lpfc_parse_vpd(phba, lpfc_vpd_data, offset);

	kfree(lpfc_vpd_data);
out_free_mbox:
	mempool_free(pmb, phba->mbox_mem_pool);
	return 0;
}

/**
 * lpfc_config_async_cmpl - Completion handler for config async event mbox cmd
 * @phba: pointer to lpfc hba data structure.
 * @pmboxq: pointer to the driver internal queue element for mailbox command.
 *
 * This is the completion handler for driver's configuring asynchronous event
 * mailbox command to the device. If the mailbox command returns successfully,
 * it will set internal async event support flag to 1; otherwise, it will
 * set internal async event support flag to 0.
 **/
static void
lpfc_config_async_cmpl(struct lpfc_hba * phba, LPFC_MBOXQ_t * pmboxq)
{
	if (pmboxq->u.mb.mbxStatus == MBX_SUCCESS)
		phba->temp_sensor_support = 1;
	else
		phba->temp_sensor_support = 0;
	mempool_free(pmboxq, phba->mbox_mem_pool);
	return;
}

/**
 * lpfc_dump_wakeup_param_cmpl - dump memory mailbox command completion handler
 * @phba: pointer to lpfc hba data structure.
 * @pmboxq: pointer to the driver internal queue element for mailbox command.
 *
 * This is the completion handler for dump mailbox command for getting
 * wake up parameters. When this command complete, the response contain
 * Option rom version of the HBA. This function translate the version number
 * into a human readable string and store it in OptionROMVersion.
 **/
static void
lpfc_dump_wakeup_param_cmpl(struct lpfc_hba *phba, LPFC_MBOXQ_t *pmboxq)
{
	struct prog_id *prg;
	uint32_t prog_id_word;
	char dist = ' ';
	/* character array used for decoding dist type. */
	char dist_char[] = "nabx";

	if (pmboxq->u.mb.mbxStatus != MBX_SUCCESS) {
		mempool_free(pmboxq, phba->mbox_mem_pool);
		return;
	}

	prg = (struct prog_id *) &prog_id_word;

	/* word 7 contain option rom version */
	prog_id_word = pmboxq->u.mb.un.varWords[7];

	/* Decode the Option rom version word to a readable string */
	if (prg->dist < 4)
		dist = dist_char[prg->dist];

	if ((prg->dist == 3) && (prg->num == 0))
		snprintf(phba->OptionROMVersion, 32, "%d.%d%d",
			prg->ver, prg->rev, prg->lev);
	else
		snprintf(phba->OptionROMVersion, 32, "%d.%d%d%c%d",
			prg->ver, prg->rev, prg->lev,
			dist, prg->num);
	mempool_free(pmboxq, phba->mbox_mem_pool);
	return;
}

/**
 * lpfc_update_vport_wwn - Updates the fc_nodename, fc_portname,
 *	cfg_soft_wwnn, cfg_soft_wwpn
 * @vport: pointer to lpfc vport data structure.
 *
 *
 * Return codes
 *   None.
 **/
void
lpfc_update_vport_wwn(struct lpfc_vport *vport)
{
	/* If the soft name exists then update it using the service params */
	if (vport->phba->cfg_soft_wwnn)
		u64_to_wwn(vport->phba->cfg_soft_wwnn,
			   vport->fc_sparam.nodeName.u.wwn);
	if (vport->phba->cfg_soft_wwpn)
		u64_to_wwn(vport->phba->cfg_soft_wwpn,
			   vport->fc_sparam.portName.u.wwn);

	/*
	 * If the name is empty or there exists a soft name
	 * then copy the service params name, otherwise use the fc name
	 */
	if (vport->fc_nodename.u.wwn[0] == 0 || vport->phba->cfg_soft_wwnn)
		memcpy(&vport->fc_nodename, &vport->fc_sparam.nodeName,
			sizeof(struct lpfc_name));
	else
		memcpy(&vport->fc_sparam.nodeName, &vport->fc_nodename,
			sizeof(struct lpfc_name));

	if (vport->fc_portname.u.wwn[0] == 0 || vport->phba->cfg_soft_wwpn)
		memcpy(&vport->fc_portname, &vport->fc_sparam.portName,
			sizeof(struct lpfc_name));
	else
		memcpy(&vport->fc_sparam.portName, &vport->fc_portname,
			sizeof(struct lpfc_name));
}

/**
 * lpfc_config_port_post - Perform lpfc initialization after config port
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine will do LPFC initialization after the CONFIG_PORT mailbox
 * command call. It performs all internal resource and state setups on the
 * port: post IOCB buffers, enable appropriate host interrupt attentions,
 * ELS ring timers, etc.
 *
 * Return codes
 *   0 - success.
 *   Any other value - error.
 **/
int
lpfc_config_port_post(struct lpfc_hba *phba)
{
	struct lpfc_vport *vport = phba->pport;
	struct Scsi_Host *shost = lpfc_shost_from_vport(vport);
	LPFC_MBOXQ_t *pmb;
	MAILBOX_t *mb;
	struct lpfc_dmabuf *mp;
	struct lpfc_sli *psli = &phba->sli;
	uint32_t status, timeout;
	int i, j;
	int rc;

	spin_lock_irq(&phba->hbalock);
	/*
	 * If the Config port completed correctly the HBA is not
	 * over heated any more.
	 */
	if (phba->over_temp_state == HBA_OVER_TEMP)
		phba->over_temp_state = HBA_NORMAL_TEMP;
	spin_unlock_irq(&phba->hbalock);

	pmb = mempool_alloc(phba->mbox_mem_pool, GFP_KERNEL);
	if (!pmb) {
		phba->link_state = LPFC_HBA_ERROR;
		return -ENOMEM;
	}
	mb = &pmb->u.mb;

	/* Get login parameters for NID.  */
	rc = lpfc_read_sparam(phba, pmb, 0);
	if (rc) {
		mempool_free(pmb, phba->mbox_mem_pool);
		return -ENOMEM;
	}

	pmb->vport = vport;
	if (lpfc_sli_issue_mbox(phba, pmb, MBX_POLL) != MBX_SUCCESS) {
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0448 Adapter failed init, mbxCmd x%x "
				"READ_SPARM mbxStatus x%x\n",
				mb->mbxCommand, mb->mbxStatus);
		phba->link_state = LPFC_HBA_ERROR;
		mp = (struct lpfc_dmabuf *) pmb->context1;
		mempool_free(pmb, phba->mbox_mem_pool);
		lpfc_mbuf_free(phba, mp->virt, mp->phys);
		kfree(mp);
		return -EIO;
	}

	mp = (struct lpfc_dmabuf *) pmb->context1;

	memcpy(&vport->fc_sparam, mp->virt, sizeof (struct serv_parm));
	lpfc_mbuf_free(phba, mp->virt, mp->phys);
	kfree(mp);
	pmb->context1 = NULL;
	lpfc_update_vport_wwn(vport);

	/* Update the fc_host data structures with new wwn. */
	fc_host_node_name(shost) = wwn_to_u64(vport->fc_nodename.u.wwn);
	fc_host_port_name(shost) = wwn_to_u64(vport->fc_portname.u.wwn);
	fc_host_max_npiv_vports(shost) = phba->max_vpi;

	/* If no serial number in VPD data, use low 6 bytes of WWNN */
	/* This should be consolidated into parse_vpd ? - mr */
	if (phba->SerialNumber[0] == 0) {
		uint8_t *outptr;

		outptr = &vport->fc_nodename.u.s.IEEE[0];
		for (i = 0; i < 12; i++) {
			status = *outptr++;
			j = ((status & 0xf0) >> 4);
			if (j <= 9)
				phba->SerialNumber[i] =
				    (char)((uint8_t) 0x30 + (uint8_t) j);
			else
				phba->SerialNumber[i] =
				    (char)((uint8_t) 0x61 + (uint8_t) (j - 10));
			i++;
			j = (status & 0xf);
			if (j <= 9)
				phba->SerialNumber[i] =
				    (char)((uint8_t) 0x30 + (uint8_t) j);
			else
				phba->SerialNumber[i] =
				    (char)((uint8_t) 0x61 + (uint8_t) (j - 10));
		}
	}

	lpfc_read_config(phba, pmb);
	pmb->vport = vport;
	if (lpfc_sli_issue_mbox(phba, pmb, MBX_POLL) != MBX_SUCCESS) {
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0453 Adapter failed to init, mbxCmd x%x "
				"READ_CONFIG, mbxStatus x%x\n",
				mb->mbxCommand, mb->mbxStatus);
		phba->link_state = LPFC_HBA_ERROR;
		mempool_free( pmb, phba->mbox_mem_pool);
		return -EIO;
	}

	/* Check if the port is disabled */
	lpfc_sli_read_link_ste(phba);

	/* Reset the DFT_HBA_Q_DEPTH to the max xri  */
	i = (mb->un.varRdConfig.max_xri + 1);
	if (phba->cfg_hba_queue_depth > i) {
		lpfc_printf_log(phba, KERN_WARNING, LOG_INIT,
				"3359 HBA queue depth changed from %d to %d\n",
				phba->cfg_hba_queue_depth, i);
		phba->cfg_hba_queue_depth = i;
	}

	/* Reset the DFT_LUN_Q_DEPTH to (max xri >> 3)  */
	i = (mb->un.varRdConfig.max_xri >> 3);
	if (phba->pport->cfg_lun_queue_depth > i) {
		lpfc_printf_log(phba, KERN_WARNING, LOG_INIT,
				"3360 LUN queue depth changed from %d to %d\n",
				phba->pport->cfg_lun_queue_depth, i);
		phba->pport->cfg_lun_queue_depth = i;
	}

	phba->lmt = mb->un.varRdConfig.lmt;

	/* Get the default values for Model Name and Description */
	lpfc_get_hba_model_desc(phba, phba->ModelName, phba->ModelDesc);

	phba->link_state = LPFC_LINK_DOWN;

	/* Only process IOCBs on ELS ring till hba_state is READY */
	if (psli->ring[psli->extra_ring].sli.sli3.cmdringaddr)
		psli->ring[psli->extra_ring].flag |= LPFC_STOP_IOCB_EVENT;
	if (psli->ring[psli->fcp_ring].sli.sli3.cmdringaddr)
		psli->ring[psli->fcp_ring].flag |= LPFC_STOP_IOCB_EVENT;
	if (psli->ring[psli->next_ring].sli.sli3.cmdringaddr)
		psli->ring[psli->next_ring].flag |= LPFC_STOP_IOCB_EVENT;

	/* Post receive buffers for desired rings */
	if (phba->sli_rev != 3)
		lpfc_post_rcv_buf(phba);

	/*
	 * Configure HBA MSI-X attention conditions to messages if MSI-X mode
	 */
	if (phba->intr_type == MSIX) {
		rc = lpfc_config_msi(phba, pmb);
		if (rc) {
			mempool_free(pmb, phba->mbox_mem_pool);
			return -EIO;
		}
		rc = lpfc_sli_issue_mbox(phba, pmb, MBX_POLL);
		if (rc != MBX_SUCCESS) {
			lpfc_printf_log(phba, KERN_ERR, LOG_MBOX,
					"0352 Config MSI mailbox command "
					"failed, mbxCmd x%x, mbxStatus x%x\n",
					pmb->u.mb.mbxCommand,
					pmb->u.mb.mbxStatus);
			mempool_free(pmb, phba->mbox_mem_pool);
			return -EIO;
		}
	}

	spin_lock_irq(&phba->hbalock);
	/* Initialize ERATT handling flag */
	phba->hba_flag &= ~HBA_ERATT_HANDLED;

	/* Enable appropriate host interrupts */
	if (lpfc_readl(phba->HCregaddr, &status)) {
		spin_unlock_irq(&phba->hbalock);
		return -EIO;
	}
	status |= HC_MBINT_ENA | HC_ERINT_ENA | HC_LAINT_ENA;
	if (psli->num_rings > 0)
		status |= HC_R0INT_ENA;
	if (psli->num_rings > 1)
		status |= HC_R1INT_ENA;
	if (psli->num_rings > 2)
		status |= HC_R2INT_ENA;
	if (psli->num_rings > 3)
		status |= HC_R3INT_ENA;

	if ((phba->cfg_poll & ENABLE_FCP_RING_POLLING) &&
	    (phba->cfg_poll & DISABLE_FCP_RING_INT))
		status &= ~(HC_R0INT_ENA);

	writel(status, phba->HCregaddr);
	readl(phba->HCregaddr); /* flush */
	spin_unlock_irq(&phba->hbalock);

	/* Set up ring-0 (ELS) timer */
	timeout = phba->fc_ratov * 2;
	mod_timer(&vport->els_tmofunc,
		  jiffies + msecs_to_jiffies(1000 * timeout));
	/* Set up heart beat (HB) timer */
	mod_timer(&phba->hb_tmofunc,
		  jiffies + msecs_to_jiffies(1000 * LPFC_HB_MBOX_INTERVAL));
	phba->hb_outstanding = 0;
	phba->last_completion_time = jiffies;
	/* Set up error attention (ERATT) polling timer */
	mod_timer(&phba->eratt_poll,
		  jiffies + msecs_to_jiffies(1000 * LPFC_ERATT_POLL_INTERVAL));

	if (phba->hba_flag & LINK_DISABLED) {
		lpfc_printf_log(phba,
			KERN_ERR, LOG_INIT,
			"2598 Adapter Link is disabled.\n");
		lpfc_down_link(phba, pmb);
		pmb->mbox_cmpl = lpfc_sli_def_mbox_cmpl;
		rc = lpfc_sli_issue_mbox(phba, pmb, MBX_NOWAIT);
		if ((rc != MBX_SUCCESS) && (rc != MBX_BUSY)) {
			lpfc_printf_log(phba,
			KERN_ERR, LOG_INIT,
			"2599 Adapter failed to issue DOWN_LINK"
			" mbox command rc 0x%x\n", rc);

			mempool_free(pmb, phba->mbox_mem_pool);
			return -EIO;
		}
	} else if (phba->cfg_suppress_link_up == LPFC_INITIALIZE_LINK) {
		mempool_free(pmb, phba->mbox_mem_pool);
		rc = phba->lpfc_hba_init_link(phba, MBX_NOWAIT);
		if (rc)
			return rc;
	}
	/* MBOX buffer will be freed in mbox compl */
	pmb = mempool_alloc(phba->mbox_mem_pool, GFP_KERNEL);
	if (!pmb) {
		phba->link_state = LPFC_HBA_ERROR;
		return -ENOMEM;
	}

	lpfc_config_async(phba, pmb, LPFC_ELS_RING);
	pmb->mbox_cmpl = lpfc_config_async_cmpl;
	pmb->vport = phba->pport;
	rc = lpfc_sli_issue_mbox(phba, pmb, MBX_NOWAIT);

	if ((rc != MBX_BUSY) && (rc != MBX_SUCCESS)) {
		lpfc_printf_log(phba,
				KERN_ERR,
				LOG_INIT,
				"0456 Adapter failed to issue "
				"ASYNCEVT_ENABLE mbox status x%x\n",
				rc);
		mempool_free(pmb, phba->mbox_mem_pool);
	}

	/* Get Option rom version */
	pmb = mempool_alloc(phba->mbox_mem_pool, GFP_KERNEL);
	if (!pmb) {
		phba->link_state = LPFC_HBA_ERROR;
		return -ENOMEM;
	}

	lpfc_dump_wakeup_param(phba, pmb);
	pmb->mbox_cmpl = lpfc_dump_wakeup_param_cmpl;
	pmb->vport = phba->pport;
	rc = lpfc_sli_issue_mbox(phba, pmb, MBX_NOWAIT);

	if ((rc != MBX_BUSY) && (rc != MBX_SUCCESS)) {
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT, "0435 Adapter failed "
				"to get Option ROM version status x%x\n", rc);
		mempool_free(pmb, phba->mbox_mem_pool);
	}

	return 0;
}

/**
 * lpfc_hba_init_link - Initialize the FC link
 * @phba: pointer to lpfc hba data structure.
 * @flag: mailbox command issue mode - either MBX_POLL or MBX_NOWAIT
 *
 * This routine will issue the INIT_LINK mailbox command call.
 * It is available to other drivers through the lpfc_hba data
 * structure for use as a delayed link up mechanism with the
 * module parameter lpfc_suppress_link_up.
 *
 * Return code
 *		0 - success
 *		Any other value - error
 **/
static int
lpfc_hba_init_link(struct lpfc_hba *phba, uint32_t flag)
{
	return lpfc_hba_init_link_fc_topology(phba, phba->cfg_topology, flag);
}

/**
 * lpfc_hba_init_link_fc_topology - Initialize FC link with desired topology
 * @phba: pointer to lpfc hba data structure.
 * @fc_topology: desired fc topology.
 * @flag: mailbox command issue mode - either MBX_POLL or MBX_NOWAIT
 *
 * This routine will issue the INIT_LINK mailbox command call.
 * It is available to other drivers through the lpfc_hba data
 * structure for use as a delayed link up mechanism with the
 * module parameter lpfc_suppress_link_up.
 *
 * Return code
 *              0 - success
 *              Any other value - error
 **/
int
lpfc_hba_init_link_fc_topology(struct lpfc_hba *phba, uint32_t fc_topology,
			       uint32_t flag)
{
	struct lpfc_vport *vport = phba->pport;
	LPFC_MBOXQ_t *pmb;
	MAILBOX_t *mb;
	int rc;

	pmb = mempool_alloc(phba->mbox_mem_pool, GFP_KERNEL);
	if (!pmb) {
		phba->link_state = LPFC_HBA_ERROR;
		return -ENOMEM;
	}
	mb = &pmb->u.mb;
	pmb->vport = vport;

	if ((phba->cfg_link_speed > LPFC_USER_LINK_SPEED_MAX) ||
	    ((phba->cfg_link_speed == LPFC_USER_LINK_SPEED_1G) &&
	     !(phba->lmt & LMT_1Gb)) ||
	    ((phba->cfg_link_speed == LPFC_USER_LINK_SPEED_2G) &&
	     !(phba->lmt & LMT_2Gb)) ||
	    ((phba->cfg_link_speed == LPFC_USER_LINK_SPEED_4G) &&
	     !(phba->lmt & LMT_4Gb)) ||
	    ((phba->cfg_link_speed == LPFC_USER_LINK_SPEED_8G) &&
	     !(phba->lmt & LMT_8Gb)) ||
	    ((phba->cfg_link_speed == LPFC_USER_LINK_SPEED_10G) &&
	     !(phba->lmt & LMT_10Gb)) ||
	    ((phba->cfg_link_speed == LPFC_USER_LINK_SPEED_16G) &&
	     !(phba->lmt & LMT_16Gb))) {
		/* Reset link speed to auto */
		lpfc_printf_log(phba, KERN_ERR, LOG_LINK_EVENT,
			"1302 Invalid speed for this board:%d "
			"Reset link speed to auto.\n",
			phba->cfg_link_speed);
			phba->cfg_link_speed = LPFC_USER_LINK_SPEED_AUTO;
	}
	lpfc_init_link(phba, pmb, fc_topology, phba->cfg_link_speed);
	pmb->mbox_cmpl = lpfc_sli_def_mbox_cmpl;
	if (phba->sli_rev < LPFC_SLI_REV4)
		lpfc_set_loopback_flag(phba);
	rc = lpfc_sli_issue_mbox(phba, pmb, flag);
	if ((rc != MBX_BUSY) && (rc != MBX_SUCCESS)) {
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
			"0498 Adapter failed to init, mbxCmd x%x "
			"INIT_LINK, mbxStatus x%x\n",
			mb->mbxCommand, mb->mbxStatus);
		if (phba->sli_rev <= LPFC_SLI_REV3) {
			/* Clear all interrupt enable conditions */
			writel(0, phba->HCregaddr);
			readl(phba->HCregaddr); /* flush */
			/* Clear all pending interrupts */
			writel(0xffffffff, phba->HAregaddr);
			readl(phba->HAregaddr); /* flush */
		}
		phba->link_state = LPFC_HBA_ERROR;
		if (rc != MBX_BUSY || flag == MBX_POLL)
			mempool_free(pmb, phba->mbox_mem_pool);
		return -EIO;
	}
	phba->cfg_suppress_link_up = LPFC_INITIALIZE_LINK;
	if (flag == MBX_POLL)
		mempool_free(pmb, phba->mbox_mem_pool);

	return 0;
}

/**
 * lpfc_hba_down_link - this routine downs the FC link
 * @phba: pointer to lpfc hba data structure.
 * @flag: mailbox command issue mode - either MBX_POLL or MBX_NOWAIT
 *
 * This routine will issue the DOWN_LINK mailbox command call.
 * It is available to other drivers through the lpfc_hba data
 * structure for use to stop the link.
 *
 * Return code
 *		0 - success
 *		Any other value - error
 **/
static int
lpfc_hba_down_link(struct lpfc_hba *phba, uint32_t flag)
{
	LPFC_MBOXQ_t *pmb;
	int rc;

	pmb = mempool_alloc(phba->mbox_mem_pool, GFP_KERNEL);
	if (!pmb) {
		phba->link_state = LPFC_HBA_ERROR;
		return -ENOMEM;
	}

	lpfc_printf_log(phba,
		KERN_ERR, LOG_INIT,
		"0491 Adapter Link is disabled.\n");
	lpfc_down_link(phba, pmb);
	pmb->mbox_cmpl = lpfc_sli_def_mbox_cmpl;
	rc = lpfc_sli_issue_mbox(phba, pmb, flag);
	if ((rc != MBX_SUCCESS) && (rc != MBX_BUSY)) {
		lpfc_printf_log(phba,
		KERN_ERR, LOG_INIT,
		"2522 Adapter failed to issue DOWN_LINK"
		" mbox command rc 0x%x\n", rc);

		mempool_free(pmb, phba->mbox_mem_pool);
		return -EIO;
	}
	if (flag == MBX_POLL)
		mempool_free(pmb, phba->mbox_mem_pool);

	return 0;
}

/**
 * lpfc_hba_down_prep - Perform lpfc uninitialization prior to HBA reset
 * @phba: pointer to lpfc HBA data structure.
 *
 * This routine will do LPFC uninitialization before the HBA is reset when
 * bringing down the SLI Layer.
 *
 * Return codes
 *   0 - success.
 *   Any other value - error.
 **/
int
lpfc_hba_down_prep(struct lpfc_hba *phba)
{
	struct lpfc_vport **vports;
	int i;

	if (phba->sli_rev <= LPFC_SLI_REV3) {
		/* Disable interrupts */
		writel(0, phba->HCregaddr);
		readl(phba->HCregaddr); /* flush */
	}

	if (phba->pport->load_flag & FC_UNLOADING)
		lpfc_cleanup_discovery_resources(phba->pport);
	else {
		vports = lpfc_create_vport_work_array(phba);
		if (vports != NULL)
			for (i = 0; i <= phba->max_vports &&
				vports[i] != NULL; i++)
				lpfc_cleanup_discovery_resources(vports[i]);
		lpfc_destroy_vport_work_array(phba, vports);
	}
	return 0;
}

/**
 * lpfc_sli4_free_sp_events - Cleanup sp_queue_events to free
 * rspiocb which got deferred
 *
 * @phba: pointer to lpfc HBA data structure.
 *
 * This routine will cleanup completed slow path events after HBA is reset
 * when bringing down the SLI Layer.
 *
 *
 * Return codes
 *   void.
 **/
static void
lpfc_sli4_free_sp_events(struct lpfc_hba *phba)
{
	struct lpfc_iocbq *rspiocbq;
	struct hbq_dmabuf *dmabuf;
	struct lpfc_cq_event *cq_event;

	spin_lock_irq(&phba->hbalock);
	phba->hba_flag &= ~HBA_SP_QUEUE_EVT;
	spin_unlock_irq(&phba->hbalock);

	while (!list_empty(&phba->sli4_hba.sp_queue_event)) {
		/* Get the response iocb from the head of work queue */
		spin_lock_irq(&phba->hbalock);
		list_remove_head(&phba->sli4_hba.sp_queue_event,
				 cq_event, struct lpfc_cq_event, list);
		spin_unlock_irq(&phba->hbalock);

		switch (bf_get(lpfc_wcqe_c_code, &cq_event->cqe.wcqe_cmpl)) {
		case CQE_CODE_COMPL_WQE:
			rspiocbq = container_of(cq_event, struct lpfc_iocbq,
						 cq_event);
			lpfc_sli_release_iocbq(phba, rspiocbq);
			break;
		case CQE_CODE_RECEIVE:
		case CQE_CODE_RECEIVE_V1:
			dmabuf = container_of(cq_event, struct hbq_dmabuf,
					      cq_event);
			lpfc_in_buf_free(phba, &dmabuf->dbuf);
		}
	}
}

/**
 * lpfc_hba_free_post_buf - Perform lpfc uninitialization after HBA reset
 * @phba: pointer to lpfc HBA data structure.
 *
 * This routine will cleanup posted ELS buffers after the HBA is reset
 * when bringing down the SLI Layer.
 *
 *
 * Return codes
 *   void.
 **/
static void
lpfc_hba_free_post_buf(struct lpfc_hba *phba)
{
	struct lpfc_sli *psli = &phba->sli;
	struct lpfc_sli_ring *pring;
	struct lpfc_dmabuf *mp, *next_mp;
	LIST_HEAD(buflist);
	int count;

	if (phba->sli3_options & LPFC_SLI3_HBQ_ENABLED)
		lpfc_sli_hbqbuf_free_all(phba);
	else {
		/* Cleanup preposted buffers on the ELS ring */
		pring = &psli->ring[LPFC_ELS_RING];
		spin_lock_irq(&phba->hbalock);
		list_splice_init(&pring->postbufq, &buflist);
		spin_unlock_irq(&phba->hbalock);

		count = 0;
		list_for_each_entry_safe(mp, next_mp, &buflist, list) {
			list_del(&mp->list);
			count++;
			lpfc_mbuf_free(phba, mp->virt, mp->phys);
			kfree(mp);
		}

		spin_lock_irq(&phba->hbalock);
		pring->postbufq_cnt -= count;
		spin_unlock_irq(&phba->hbalock);
	}
}

/**
 * lpfc_hba_clean_txcmplq - Perform lpfc uninitialization after HBA reset
 * @phba: pointer to lpfc HBA data structure.
 *
 * This routine will cleanup the txcmplq after the HBA is reset when bringing
 * down the SLI Layer.
 *
 * Return codes
 *   void
 **/
static void
lpfc_hba_clean_txcmplq(struct lpfc_hba *phba)
{
	struct lpfc_sli *psli = &phba->sli;
	struct lpfc_sli_ring *pring;
	LIST_HEAD(completions);
	int i;

	for (i = 0; i < psli->num_rings; i++) {
		pring = &psli->ring[i];
		if (phba->sli_rev >= LPFC_SLI_REV4)
			spin_lock_irq(&pring->ring_lock);
		else
			spin_lock_irq(&phba->hbalock);
		/* At this point in time the HBA is either reset or DOA. Either
		 * way, nothing should be on txcmplq as it will NEVER complete.
		 */
		list_splice_init(&pring->txcmplq, &completions);
		pring->txcmplq_cnt = 0;

		if (phba->sli_rev >= LPFC_SLI_REV4)
			spin_unlock_irq(&pring->ring_lock);
		else
			spin_unlock_irq(&phba->hbalock);

		/* Cancel all the IOCBs from the completions list */
		lpfc_sli_cancel_iocbs(phba, &completions, IOSTAT_LOCAL_REJECT,
				      IOERR_SLI_ABORTED);
		lpfc_sli_abort_iocb_ring(phba, pring);
	}
}

/**
 * lpfc_hba_down_post_s3 - Perform lpfc uninitialization after HBA reset
	int i;
 * @phba: pointer to lpfc HBA data structure.
 *
 * This routine will do uninitialization after the HBA is reset when bring
 * down the SLI Layer.
 *
 * Return codes
 *   0 - success.
 *   Any other value - error.
 **/
static int
lpfc_hba_down_post_s3(struct lpfc_hba *phba)
{
	lpfc_hba_free_post_buf(phba);
	lpfc_hba_clean_txcmplq(phba);
	return 0;
}

/**
 * lpfc_hba_down_post_s4 - Perform lpfc uninitialization after HBA reset
 * @phba: pointer to lpfc HBA data structure.
 *
 * This routine will do uninitialization after the HBA is reset when bring
 * down the SLI Layer.
 *
 * Return codes
 *   0 - success.
 *   Any other value - error.
 **/
static int
lpfc_hba_down_post_s4(struct lpfc_hba *phba)
{
	struct lpfc_scsi_buf *psb, *psb_next;
	LIST_HEAD(aborts);
	unsigned long iflag = 0;
	struct lpfc_sglq *sglq_entry = NULL;
	struct lpfc_sli *psli = &phba->sli;
	struct lpfc_sli_ring *pring;

	lpfc_hba_free_post_buf(phba);
	lpfc_hba_clean_txcmplq(phba);
	pring = &psli->ring[LPFC_ELS_RING];

	/* At this point in time the HBA is either reset or DOA. Either
	 * way, nothing should be on lpfc_abts_els_sgl_list, it needs to be
	 * on the lpfc_sgl_list so that it can either be freed if the
	 * driver is unloading or reposted if the driver is restarting
	 * the port.
	 */
	spin_lock_irq(&phba->hbalock);  /* required for lpfc_sgl_list and */
					/* scsl_buf_list */
	/* abts_sgl_list_lock required because worker thread uses this
	 * list.
	 */
	spin_lock(&phba->sli4_hba.abts_sgl_list_lock);
	list_for_each_entry(sglq_entry,
		&phba->sli4_hba.lpfc_abts_els_sgl_list, list)
		sglq_entry->state = SGL_FREED;

	spin_lock(&pring->ring_lock);
	list_splice_init(&phba->sli4_hba.lpfc_abts_els_sgl_list,
			&phba->sli4_hba.lpfc_sgl_list);
	spin_unlock(&pring->ring_lock);
	spin_unlock(&phba->sli4_hba.abts_sgl_list_lock);
	/* abts_scsi_buf_list_lock required because worker thread uses this
	 * list.
	 */
	spin_lock(&phba->sli4_hba.abts_scsi_buf_list_lock);
	list_splice_init(&phba->sli4_hba.lpfc_abts_scsi_buf_list,
			&aborts);
	spin_unlock(&phba->sli4_hba.abts_scsi_buf_list_lock);
	spin_unlock_irq(&phba->hbalock);

	list_for_each_entry_safe(psb, psb_next, &aborts, list) {
		psb->pCmd = NULL;
		psb->status = IOSTAT_SUCCESS;
	}
	spin_lock_irqsave(&phba->scsi_buf_list_put_lock, iflag);
	list_splice(&aborts, &phba->lpfc_scsi_buf_list_put);
	spin_unlock_irqrestore(&phba->scsi_buf_list_put_lock, iflag);

	lpfc_sli4_free_sp_events(phba);
	return 0;
}

/**
 * lpfc_hba_down_post - Wrapper func for hba down post routine
 * @phba: pointer to lpfc HBA data structure.
 *
 * This routine wraps the actual SLI3 or SLI4 routine for performing
 * uninitialization after the HBA is reset when bring down the SLI Layer.
 *
 * Return codes
 *   0 - success.
 *   Any other value - error.
 **/
int
lpfc_hba_down_post(struct lpfc_hba *phba)
{
	return (*phba->lpfc_hba_down_post)(phba);
}

/**
 * lpfc_hb_timeout - The HBA-timer timeout handler
 * @ptr: unsigned long holds the pointer to lpfc hba data structure.
 *
 * This is the HBA-timer timeout handler registered to the lpfc driver. When
 * this timer fires, a HBA timeout event shall be posted to the lpfc driver
 * work-port-events bitmap and the worker thread is notified. This timeout
 * event will be used by the worker thread to invoke the actual timeout
 * handler routine, lpfc_hb_timeout_handler. Any periodical operations will
 * be performed in the timeout handler and the HBA timeout event bit shall
 * be cleared by the worker thread after it has taken the event bitmap out.
 **/
static void
lpfc_hb_timeout(unsigned long ptr)
{
	struct lpfc_hba *phba;
	uint32_t tmo_posted;
	unsigned long iflag;

	phba = (struct lpfc_hba *)ptr;

	/* Check for heart beat timeout conditions */
	spin_lock_irqsave(&phba->pport->work_port_lock, iflag);
	tmo_posted = phba->pport->work_port_events & WORKER_HB_TMO;
	if (!tmo_posted)
		phba->pport->work_port_events |= WORKER_HB_TMO;
	spin_unlock_irqrestore(&phba->pport->work_port_lock, iflag);

	/* Tell the worker thread there is work to do */
	if (!tmo_posted)
		lpfc_worker_wake_up(phba);
	return;
}

/**
 * lpfc_rrq_timeout - The RRQ-timer timeout handler
 * @ptr: unsigned long holds the pointer to lpfc hba data structure.
 *
 * This is the RRQ-timer timeout handler registered to the lpfc driver. When
 * this timer fires, a RRQ timeout event shall be posted to the lpfc driver
 * work-port-events bitmap and the worker thread is notified. This timeout
 * event will be used by the worker thread to invoke the actual timeout
 * handler routine, lpfc_rrq_handler. Any periodical operations will
 * be performed in the timeout handler and the RRQ timeout event bit shall
 * be cleared by the worker thread after it has taken the event bitmap out.
 **/
static void
lpfc_rrq_timeout(unsigned long ptr)
{
	struct lpfc_hba *phba;
	unsigned long iflag;

	phba = (struct lpfc_hba *)ptr;
	spin_lock_irqsave(&phba->pport->work_port_lock, iflag);
	if (!(phba->pport->load_flag & FC_UNLOADING))
		phba->hba_flag |= HBA_RRQ_ACTIVE;
	else
		phba->hba_flag &= ~HBA_RRQ_ACTIVE;
	spin_unlock_irqrestore(&phba->pport->work_port_lock, iflag);

	if (!(phba->pport->load_flag & FC_UNLOADING))
		lpfc_worker_wake_up(phba);
}

/**
 * lpfc_hb_mbox_cmpl - The lpfc heart-beat mailbox command callback function
 * @phba: pointer to lpfc hba data structure.
 * @pmboxq: pointer to the driver internal queue element for mailbox command.
 *
 * This is the callback function to the lpfc heart-beat mailbox command.
 * If configured, the lpfc driver issues the heart-beat mailbox command to
 * the HBA every LPFC_HB_MBOX_INTERVAL (current 5) seconds. At the time the
 * heart-beat mailbox command is issued, the driver shall set up heart-beat
 * timeout timer to LPFC_HB_MBOX_TIMEOUT (current 30) seconds and marks
 * heart-beat outstanding state. Once the mailbox command comes back and
 * no error conditions detected, the heart-beat mailbox command timer is
 * reset to LPFC_HB_MBOX_INTERVAL seconds and the heart-beat outstanding
 * state is cleared for the next heart-beat. If the timer expired with the
 * heart-beat outstanding state set, the driver will put the HBA offline.
 **/
static void
lpfc_hb_mbox_cmpl(struct lpfc_hba * phba, LPFC_MBOXQ_t * pmboxq)
{
	unsigned long drvr_flag;

	spin_lock_irqsave(&phba->hbalock, drvr_flag);
	phba->hb_outstanding = 0;
	spin_unlock_irqrestore(&phba->hbalock, drvr_flag);

	/* Check and reset heart-beat timer is necessary */
	mempool_free(pmboxq, phba->mbox_mem_pool);
	if (!(phba->pport->fc_flag & FC_OFFLINE_MODE) &&
		!(phba->link_state == LPFC_HBA_ERROR) &&
		!(phba->pport->load_flag & FC_UNLOADING))
		mod_timer(&phba->hb_tmofunc,
			  jiffies +
			  msecs_to_jiffies(1000 * LPFC_HB_MBOX_INTERVAL));
	return;
}

/**
 * lpfc_hb_timeout_handler - The HBA-timer timeout handler
 * @phba: pointer to lpfc hba data structure.
 *
 * This is the actual HBA-timer timeout handler to be invoked by the worker
 * thread whenever the HBA timer fired and HBA-timeout event posted. This
 * handler performs any periodic operations needed for the device. If such
 * periodic event has already been attended to either in the interrupt handler
 * or by processing slow-ring or fast-ring events within the HBA-timer
 * timeout window (LPFC_HB_MBOX_INTERVAL), this handler just simply resets
 * the timer for the next timeout period. If lpfc heart-beat mailbox command
 * is configured and there is no heart-beat mailbox command outstanding, a
 * heart-beat mailbox is issued and timer set properly. Otherwise, if there
 * has been a heart-beat mailbox command outstanding, the HBA shall be put
 * to offline.
 **/
void
lpfc_hb_timeout_handler(struct lpfc_hba *phba)
{
	struct lpfc_vport **vports;
	LPFC_MBOXQ_t *pmboxq;
	struct lpfc_dmabuf *buf_ptr;
	int retval, i;
	struct lpfc_sli *psli = &phba->sli;
	LIST_HEAD(completions);

	vports = lpfc_create_vport_work_array(phba);
	if (vports != NULL)
		for (i = 0; i <= phba->max_vports && vports[i] != NULL; i++)
			lpfc_rcv_seq_check_edtov(vports[i]);
	lpfc_destroy_vport_work_array(phba, vports);

	if ((phba->link_state == LPFC_HBA_ERROR) ||
		(phba->pport->load_flag & FC_UNLOADING) ||
		(phba->pport->fc_flag & FC_OFFLINE_MODE))
		return;

	spin_lock_irq(&phba->pport->work_port_lock);

	if (time_after(phba->last_completion_time +
			msecs_to_jiffies(1000 * LPFC_HB_MBOX_INTERVAL),
			jiffies)) {
		spin_unlock_irq(&phba->pport->work_port_lock);
		if (!phba->hb_outstanding)
			mod_timer(&phba->hb_tmofunc,
				jiffies +
				msecs_to_jiffies(1000 * LPFC_HB_MBOX_INTERVAL));
		else
			mod_timer(&phba->hb_tmofunc,
				jiffies +
				msecs_to_jiffies(1000 * LPFC_HB_MBOX_TIMEOUT));
		return;
	}
	spin_unlock_irq(&phba->pport->work_port_lock);

	if (phba->elsbuf_cnt &&
		(phba->elsbuf_cnt == phba->elsbuf_prev_cnt)) {
		spin_lock_irq(&phba->hbalock);
		list_splice_init(&phba->elsbuf, &completions);
		phba->elsbuf_cnt = 0;
		phba->elsbuf_prev_cnt = 0;
		spin_unlock_irq(&phba->hbalock);

		while (!list_empty(&completions)) {
			list_remove_head(&completions, buf_ptr,
				struct lpfc_dmabuf, list);
			lpfc_mbuf_free(phba, buf_ptr->virt, buf_ptr->phys);
			kfree(buf_ptr);
		}
	}
	phba->elsbuf_prev_cnt = phba->elsbuf_cnt;

	/* If there is no heart beat outstanding, issue a heartbeat command */
	if (phba->cfg_enable_hba_heartbeat) {
		if (!phba->hb_outstanding) {
			if ((!(psli->sli_flag & LPFC_SLI_MBOX_ACTIVE)) &&
				(list_empty(&psli->mboxq))) {
				pmboxq = mempool_alloc(phba->mbox_mem_pool,
							GFP_KERNEL);
				if (!pmboxq) {
					mod_timer(&phba->hb_tmofunc,
						 jiffies +
						 msecs_to_jiffies(1000 *
						 LPFC_HB_MBOX_INTERVAL));
					return;
				}

				lpfc_heart_beat(phba, pmboxq);
				pmboxq->mbox_cmpl = lpfc_hb_mbox_cmpl;
				pmboxq->vport = phba->pport;
				retval = lpfc_sli_issue_mbox(phba, pmboxq,
						MBX_NOWAIT);

				if (retval != MBX_BUSY &&
					retval != MBX_SUCCESS) {
					mempool_free(pmboxq,
							phba->mbox_mem_pool);
					mod_timer(&phba->hb_tmofunc,
						jiffies +
						msecs_to_jiffies(1000 *
						LPFC_HB_MBOX_INTERVAL));
					return;
				}
				phba->skipped_hb = 0;
				phba->hb_outstanding = 1;
			} else if (time_before_eq(phba->last_completion_time,
					phba->skipped_hb)) {
				lpfc_printf_log(phba, KERN_INFO, LOG_INIT,
					"2857 Last completion time not "
					" updated in %d ms\n",
					jiffies_to_msecs(jiffies
						 - phba->last_completion_time));
			} else
				phba->skipped_hb = jiffies;

			mod_timer(&phba->hb_tmofunc,
				 jiffies +
				 msecs_to_jiffies(1000 * LPFC_HB_MBOX_TIMEOUT));
			return;
		} else {
			/*
			* If heart beat timeout called with hb_outstanding set
			* we need to give the hb mailbox cmd a chance to
			* complete or TMO.
			*/
			lpfc_printf_log(phba, KERN_WARNING, LOG_INIT,
					"0459 Adapter heartbeat still out"
					"standing:last compl time was %d ms.\n",
					jiffies_to_msecs(jiffies
						 - phba->last_completion_time));
			mod_timer(&phba->hb_tmofunc,
				jiffies +
				msecs_to_jiffies(1000 * LPFC_HB_MBOX_TIMEOUT));
		}
	}
}

/**
 * lpfc_offline_eratt - Bring lpfc offline on hardware error attention
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is called to bring the HBA offline when HBA hardware error
 * other than Port Error 6 has been detected.
 **/
static void
lpfc_offline_eratt(struct lpfc_hba *phba)
{
	struct lpfc_sli   *psli = &phba->sli;

	spin_lock_irq(&phba->hbalock);
	psli->sli_flag &= ~LPFC_SLI_ACTIVE;
	spin_unlock_irq(&phba->hbalock);
	lpfc_offline_prep(phba, LPFC_MBX_NO_WAIT);

	lpfc_offline(phba);
	lpfc_reset_barrier(phba);
	spin_lock_irq(&phba->hbalock);
	lpfc_sli_brdreset(phba);
	spin_unlock_irq(&phba->hbalock);
	lpfc_hba_down_post(phba);
	lpfc_sli_brdready(phba, HS_MBRDY);
	lpfc_unblock_mgmt_io(phba);
	phba->link_state = LPFC_HBA_ERROR;
	return;
}

/**
 * lpfc_sli4_offline_eratt - Bring lpfc offline on SLI4 hardware error attention
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is called to bring a SLI4 HBA offline when HBA hardware error
 * other than Port Error 6 has been detected.
 **/
void
lpfc_sli4_offline_eratt(struct lpfc_hba *phba)
{
	spin_lock_irq(&phba->hbalock);
	phba->link_state = LPFC_HBA_ERROR;
	spin_unlock_irq(&phba->hbalock);

	lpfc_offline_prep(phba, LPFC_MBX_NO_WAIT);
	lpfc_offline(phba);
	lpfc_hba_down_post(phba);
	lpfc_unblock_mgmt_io(phba);
}

/**
 * lpfc_handle_deferred_eratt - The HBA hardware deferred error handler
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked to handle the deferred HBA hardware error
 * conditions. This type of error is indicated by HBA by setting ER1
 * and another ER bit in the host status register. The driver will
 * wait until the ER1 bit clears before handling the error condition.
 **/
static void
lpfc_handle_deferred_eratt(struct lpfc_hba *phba)
{
	uint32_t old_host_status = phba->work_hs;
	struct lpfc_sli *psli = &phba->sli;

	/* If the pci channel is offline, ignore possible errors,
	 * since we cannot communicate with the pci card anyway.
	 */
	if (pci_channel_offline(phba->pcidev)) {
		spin_lock_irq(&phba->hbalock);
		phba->hba_flag &= ~DEFER_ERATT;
		spin_unlock_irq(&phba->hbalock);
		return;
	}

	lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
		"0479 Deferred Adapter Hardware Error "
		"Data: x%x x%x x%x\n",
		phba->work_hs,
		phba->work_status[0], phba->work_status[1]);

	spin_lock_irq(&phba->hbalock);
	psli->sli_flag &= ~LPFC_SLI_ACTIVE;
	spin_unlock_irq(&phba->hbalock);


	/*
	 * Firmware stops when it triggred erratt. That could cause the I/Os
	 * dropped by the firmware. Error iocb (I/O) on txcmplq and let the
	 * SCSI layer retry it after re-establishing link.
	 */
	lpfc_sli_abort_fcp_rings(phba);

	/*
	 * There was a firmware error. Take the hba offline and then
	 * attempt to restart it.
	 */
	lpfc_offline_prep(phba, LPFC_MBX_WAIT);
	lpfc_offline(phba);

	/* Wait for the ER1 bit to clear.*/
	while (phba->work_hs & HS_FFER1) {
		msleep(100);
		if (lpfc_readl(phba->HSregaddr, &phba->work_hs)) {
			phba->work_hs = UNPLUG_ERR ;
			break;
		}
		/* If driver is unloading let the worker thread continue */
		if (phba->pport->load_flag & FC_UNLOADING) {
			phba->work_hs = 0;
			break;
		}
	}

	/*
	 * This is to ptrotect against a race condition in which
	 * first write to the host attention register clear the
	 * host status register.
	 */
	if ((!phba->work_hs) && (!(phba->pport->load_flag & FC_UNLOADING)))
		phba->work_hs = old_host_status & ~HS_FFER1;

	spin_lock_irq(&phba->hbalock);
	phba->hba_flag &= ~DEFER_ERATT;
	spin_unlock_irq(&phba->hbalock);
	phba->work_status[0] = readl(phba->MBslimaddr + 0xa8);
	phba->work_status[1] = readl(phba->MBslimaddr + 0xac);
}

static void
lpfc_board_errevt_to_mgmt(struct lpfc_hba *phba)
{
	struct lpfc_board_event_header board_event;
	struct Scsi_Host *shost;

	board_event.event_type = FC_REG_BOARD_EVENT;
	board_event.subcategory = LPFC_EVENT_PORTINTERR;
	shost = lpfc_shost_from_vport(phba->pport);
	fc_host_post_vendor_event(shost, fc_get_event_number(),
				  sizeof(board_event),
				  (char *) &board_event,
				  LPFC_NL_VENDOR_ID);
}

/**
 * lpfc_handle_eratt_s3 - The SLI3 HBA hardware error handler
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked to handle the following HBA hardware error
 * conditions:
 * 1 - HBA error attention interrupt
 * 2 - DMA ring index out of range
 * 3 - Mailbox command came back as unknown
 **/
static void
lpfc_handle_eratt_s3(struct lpfc_hba *phba)
{
	struct lpfc_vport *vport = phba->pport;
	struct lpfc_sli   *psli = &phba->sli;
	uint32_t event_data;
	unsigned long temperature;
	struct temp_event temp_event_data;
	struct Scsi_Host  *shost;

	/* If the pci channel is offline, ignore possible errors,
	 * since we cannot communicate with the pci card anyway.
	 */
	if (pci_channel_offline(phba->pcidev)) {
		spin_lock_irq(&phba->hbalock);
		phba->hba_flag &= ~DEFER_ERATT;
		spin_unlock_irq(&phba->hbalock);
		return;
	}

	/* If resets are disabled then leave the HBA alone and return */
	if (!phba->cfg_enable_hba_reset)
		return;

	/* Send an internal error event to mgmt application */
	lpfc_board_errevt_to_mgmt(phba);

	if (phba->hba_flag & DEFER_ERATT)
		lpfc_handle_deferred_eratt(phba);

	if ((phba->work_hs & HS_FFER6) || (phba->work_hs & HS_FFER8)) {
		if (phba->work_hs & HS_FFER6)
			/* Re-establishing Link */
			lpfc_printf_log(phba, KERN_INFO, LOG_LINK_EVENT,
					"1301 Re-establishing Link "
					"Data: x%x x%x x%x\n",
					phba->work_hs, phba->work_status[0],
					phba->work_status[1]);
		if (phba->work_hs & HS_FFER8)
			/* Device Zeroization */
			lpfc_printf_log(phba, KERN_INFO, LOG_LINK_EVENT,
					"2861 Host Authentication device "
					"zeroization Data:x%x x%x x%x\n",
					phba->work_hs, phba->work_status[0],
					phba->work_status[1]);

		spin_lock_irq(&phba->hbalock);
		psli->sli_flag &= ~LPFC_SLI_ACTIVE;
		spin_unlock_irq(&phba->hbalock);

		/*
		* Firmware stops when it triggled erratt with HS_FFER6.
		* That could cause the I/Os dropped by the firmware.
		* Error iocb (I/O) on txcmplq and let the SCSI layer
		* retry it after re-establishing link.
		*/
		lpfc_sli_abort_fcp_rings(phba);

		/*
		 * There was a firmware error.  Take the hba offline and then
		 * attempt to restart it.
		 */
		lpfc_offline_prep(phba, LPFC_MBX_NO_WAIT);
		lpfc_offline(phba);
		lpfc_sli_brdrestart(phba);
		if (lpfc_online(phba) == 0) {	/* Initialize the HBA */
			lpfc_unblock_mgmt_io(phba);
			return;
		}
		lpfc_unblock_mgmt_io(phba);
	} else if (phba->work_hs & HS_CRIT_TEMP) {
		temperature = readl(phba->MBslimaddr + TEMPERATURE_OFFSET);
		temp_event_data.event_type = FC_REG_TEMPERATURE_EVENT;
		temp_event_data.event_code = LPFC_CRIT_TEMP;
		temp_event_data.data = (uint32_t)temperature;

		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0406 Adapter maximum temperature exceeded "
				"(%ld), taking this port offline "
				"Data: x%x x%x x%x\n",
				temperature, phba->work_hs,
				phba->work_status[0], phba->work_status[1]);

		shost = lpfc_shost_from_vport(phba->pport);
		fc_host_post_vendor_event(shost, fc_get_event_number(),
					  sizeof(temp_event_data),
					  (char *) &temp_event_data,
					  SCSI_NL_VID_TYPE_PCI
					  | PCI_VENDOR_ID_EMULEX);

		spin_lock_irq(&phba->hbalock);
		phba->over_temp_state = HBA_OVER_TEMP;
		spin_unlock_irq(&phba->hbalock);
		lpfc_offline_eratt(phba);

	} else {
		/* The if clause above forces this code path when the status
		 * failure is a value other than FFER6. Do not call the offline
		 * twice. This is the adapter hardware error path.
		 */
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0457 Adapter Hardware Error "
				"Data: x%x x%x x%x\n",
				phba->work_hs,
				phba->work_status[0], phba->work_status[1]);

		event_data = FC_REG_DUMP_EVENT;
		shost = lpfc_shost_from_vport(vport);
		fc_host_post_vendor_event(shost, fc_get_event_number(),
				sizeof(event_data), (char *) &event_data,
				SCSI_NL_VID_TYPE_PCI | PCI_VENDOR_ID_EMULEX);

		lpfc_offline_eratt(phba);
	}
	return;
}

/**
 * lpfc_sli4_port_sta_fn_reset - The SLI4 function reset due to port status reg
 * @phba: pointer to lpfc hba data structure.
 * @mbx_action: flag for mailbox shutdown action.
 *
 * This routine is invoked to perform an SLI4 port PCI function reset in
 * response to port status register polling attention. It waits for port
 * status register (ERR, RDY, RN) bits before proceeding with function reset.
 * During this process, interrupt vectors are freed and later requested
 * for handling possible port resource change.
 **/
static int
lpfc_sli4_port_sta_fn_reset(struct lpfc_hba *phba, int mbx_action,
			    bool en_rn_msg)
{
	int rc;
	uint32_t intr_mode;

	/*
	 * On error status condition, driver need to wait for port
	 * ready before performing reset.
	 */
	rc = lpfc_sli4_pdev_status_reg_wait(phba);
	if (!rc) {
		/* need reset: attempt for port recovery */
		if (en_rn_msg)
			lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
					"2887 Reset Needed: Attempting Port "
					"Recovery...\n");
		lpfc_offline_prep(phba, mbx_action);
		lpfc_offline(phba);
		/* release interrupt for possible resource change */
		lpfc_sli4_disable_intr(phba);
		lpfc_sli_brdrestart(phba);
		/* request and enable interrupt */
		intr_mode = lpfc_sli4_enable_intr(phba, phba->intr_mode);
		if (intr_mode == LPFC_INTR_ERROR) {
			lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
					"3175 Failed to enable interrupt\n");
			return -EIO;
		} else {
			phba->intr_mode = intr_mode;
		}
		rc = lpfc_online(phba);
		if (rc == 0)
			lpfc_unblock_mgmt_io(phba);
	}
	return rc;
}

/**
 * lpfc_handle_eratt_s4 - The SLI4 HBA hardware error handler
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked to handle the SLI4 HBA hardware error attention
 * conditions.
 **/
static void
lpfc_handle_eratt_s4(struct lpfc_hba *phba)
{
	struct lpfc_vport *vport = phba->pport;
	uint32_t event_data;
	struct Scsi_Host *shost;
	uint32_t if_type;
	struct lpfc_register portstat_reg = {0};
	uint32_t reg_err1, reg_err2;
	uint32_t uerrlo_reg, uemasklo_reg;
	uint32_t pci_rd_rc1, pci_rd_rc2;
	bool en_rn_msg = true;
	struct temp_event temp_event_data;
	int rc;

	/* If the pci channel is offline, ignore possible errors, since
	 * we cannot communicate with the pci card anyway.
	 */
	if (pci_channel_offline(phba->pcidev))
		return;

	if_type = bf_get(lpfc_sli_intf_if_type, &phba->sli4_hba.sli_intf);
	switch (if_type) {
	case LPFC_SLI_INTF_IF_TYPE_0:
		pci_rd_rc1 = lpfc_readl(
				phba->sli4_hba.u.if_type0.UERRLOregaddr,
				&uerrlo_reg);
		pci_rd_rc2 = lpfc_readl(
				phba->sli4_hba.u.if_type0.UEMASKLOregaddr,
				&uemasklo_reg);
		/* consider PCI bus read error as pci_channel_offline */
		if (pci_rd_rc1 == -EIO && pci_rd_rc2 == -EIO)
			return;
		lpfc_sli4_offline_eratt(phba);
		break;

	case LPFC_SLI_INTF_IF_TYPE_2:
		pci_rd_rc1 = lpfc_readl(
				phba->sli4_hba.u.if_type2.STATUSregaddr,
				&portstat_reg.word0);
		/* consider PCI bus read error as pci_channel_offline */
		if (pci_rd_rc1 == -EIO) {
			lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"3151 PCI bus read access failure: x%x\n",
				readl(phba->sli4_hba.u.if_type2.STATUSregaddr));
			return;
		}
		reg_err1 = readl(phba->sli4_hba.u.if_type2.ERR1regaddr);
		reg_err2 = readl(phba->sli4_hba.u.if_type2.ERR2regaddr);
		if (bf_get(lpfc_sliport_status_oti, &portstat_reg)) {
			lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"2889 Port Overtemperature event, "
				"taking port offline Data: x%x x%x\n",
				reg_err1, reg_err2);

			temp_event_data.event_type = FC_REG_TEMPERATURE_EVENT;
			temp_event_data.event_code = LPFC_CRIT_TEMP;
			temp_event_data.data = 0xFFFFFFFF;

			shost = lpfc_shost_from_vport(phba->pport);
			fc_host_post_vendor_event(shost, fc_get_event_number(),
						  sizeof(temp_event_data),
						  (char *)&temp_event_data,
						  SCSI_NL_VID_TYPE_PCI
						  | PCI_VENDOR_ID_EMULEX);

			spin_lock_irq(&phba->hbalock);
			phba->over_temp_state = HBA_OVER_TEMP;
			spin_unlock_irq(&phba->hbalock);
			lpfc_sli4_offline_eratt(phba);
			return;
		}
		if (reg_err1 == SLIPORT_ERR1_REG_ERR_CODE_2 &&
		    reg_err2 == SLIPORT_ERR2_REG_FW_RESTART) {
			lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
					"3143 Port Down: Firmware Update "
					"Detected\n");
			en_rn_msg = false;
		} else if (reg_err1 == SLIPORT_ERR1_REG_ERR_CODE_2 &&
			 reg_err2 == SLIPORT_ERR2_REG_FORCED_DUMP)
			lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
					"3144 Port Down: Debug Dump\n");
		else if (reg_err1 == SLIPORT_ERR1_REG_ERR_CODE_2 &&
			 reg_err2 == SLIPORT_ERR2_REG_FUNC_PROVISON)
			lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
					"3145 Port Down: Provisioning\n");

		/* If resets are disabled then leave the HBA alone and return */
		if (!phba->cfg_enable_hba_reset)
			return;

		/* Check port status register for function reset */
		rc = lpfc_sli4_port_sta_fn_reset(phba, LPFC_MBX_NO_WAIT,
				en_rn_msg);
		if (rc == 0) {
			/* don't report event on forced debug dump */
			if (reg_err1 == SLIPORT_ERR1_REG_ERR_CODE_2 &&
			    reg_err2 == SLIPORT_ERR2_REG_FORCED_DUMP)
				return;
			else
				break;
		}
		/* fall through for not able to recover */
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"3152 Unrecoverable error, bring the port "
				"offline\n");
		lpfc_sli4_offline_eratt(phba);
		break;
	case LPFC_SLI_INTF_IF_TYPE_1:
	default:
		break;
	}
	lpfc_printf_log(phba, KERN_WARNING, LOG_INIT,
			"3123 Report dump event to upper layer\n");
	/* Send an internal error event to mgmt application */
	lpfc_board_errevt_to_mgmt(phba);

	event_data = FC_REG_DUMP_EVENT;
	shost = lpfc_shost_from_vport(vport);
	fc_host_post_vendor_event(shost, fc_get_event_number(),
				  sizeof(event_data), (char *) &event_data,
				  SCSI_NL_VID_TYPE_PCI | PCI_VENDOR_ID_EMULEX);
}

/**
 * lpfc_handle_eratt - Wrapper func for handling hba error attention
 * @phba: pointer to lpfc HBA data structure.
 *
 * This routine wraps the actual SLI3 or SLI4 hba error attention handling
 * routine from the API jump table function pointer from the lpfc_hba struct.
 *
 * Return codes
 *   0 - success.
 *   Any other value - error.
 **/
void
lpfc_handle_eratt(struct lpfc_hba *phba)
{
	(*phba->lpfc_handle_eratt)(phba);
}

/**
 * lpfc_handle_latt - The HBA link event handler
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked from the worker thread to handle a HBA host
 * attention link event.
 **/
void
lpfc_handle_latt(struct lpfc_hba *phba)
{
	struct lpfc_vport *vport = phba->pport;
	struct lpfc_sli   *psli = &phba->sli;
	LPFC_MBOXQ_t *pmb;
	volatile uint32_t control;
	struct lpfc_dmabuf *mp;
	int rc = 0;

	pmb = (LPFC_MBOXQ_t *)mempool_alloc(phba->mbox_mem_pool, GFP_KERNEL);
	if (!pmb) {
		rc = 1;
		goto lpfc_handle_latt_err_exit;
	}

	mp = kmalloc(sizeof(struct lpfc_dmabuf), GFP_KERNEL);
	if (!mp) {
		rc = 2;
		goto lpfc_handle_latt_free_pmb;
	}

	mp->virt = lpfc_mbuf_alloc(phba, 0, &mp->phys);
	if (!mp->virt) {
		rc = 3;
		goto lpfc_handle_latt_free_mp;
	}

	/* Cleanup any outstanding ELS commands */
	lpfc_els_flush_all_cmd(phba);

	psli->slistat.link_event++;
	lpfc_read_topology(phba, pmb, mp);
	pmb->mbox_cmpl = lpfc_mbx_cmpl_read_topology;
	pmb->vport = vport;
	/* Block ELS IOCBs until we have processed this mbox command */
	phba->sli.ring[LPFC_ELS_RING].flag |= LPFC_STOP_IOCB_EVENT;
	rc = lpfc_sli_issue_mbox (phba, pmb, MBX_NOWAIT);
	if (rc == MBX_NOT_FINISHED) {
		rc = 4;
		goto lpfc_handle_latt_free_mbuf;
	}

	/* Clear Link Attention in HA REG */
	spin_lock_irq(&phba->hbalock);
	writel(HA_LATT, phba->HAregaddr);
	readl(phba->HAregaddr); /* flush */
	spin_unlock_irq(&phba->hbalock);

	return;

lpfc_handle_latt_free_mbuf:
	phba->sli.ring[LPFC_ELS_RING].flag &= ~LPFC_STOP_IOCB_EVENT;
	lpfc_mbuf_free(phba, mp->virt, mp->phys);
lpfc_handle_latt_free_mp:
	kfree(mp);
lpfc_handle_latt_free_pmb:
	mempool_free(pmb, phba->mbox_mem_pool);
lpfc_handle_latt_err_exit:
	/* Enable Link attention interrupts */
	spin_lock_irq(&phba->hbalock);
	psli->sli_flag |= LPFC_PROCESS_LA;
	control = readl(phba->HCregaddr);
	control |= HC_LAINT_ENA;
	writel(control, phba->HCregaddr);
	readl(phba->HCregaddr); /* flush */

	/* Clear Link Attention in HA REG */
	writel(HA_LATT, phba->HAregaddr);
	readl(phba->HAregaddr); /* flush */
	spin_unlock_irq(&phba->hbalock);
	lpfc_linkdown(phba);
	phba->link_state = LPFC_HBA_ERROR;

	lpfc_printf_log(phba, KERN_ERR, LOG_MBOX,
		     "0300 LATT: Cannot issue READ_LA: Data:%d\n", rc);

	return;
}

/**
 * lpfc_parse_vpd - Parse VPD (Vital Product Data)
 * @phba: pointer to lpfc hba data structure.
 * @vpd: pointer to the vital product data.
 * @len: length of the vital product data in bytes.
 *
 * This routine parses the Vital Product Data (VPD). The VPD is treated as
 * an array of characters. In this routine, the ModelName, ProgramType, and
 * ModelDesc, etc. fields of the phba data structure will be populated.
 *
 * Return codes
 *   0 - pointer to the VPD passed in is NULL
 *   1 - success
 **/
int
lpfc_parse_vpd(struct lpfc_hba *phba, uint8_t *vpd, int len)
{
	uint8_t lenlo, lenhi;
	int Length;
	int i, j;
	int finished = 0;
	int index = 0;

	if (!vpd)
		return 0;

	/* Vital Product */
	lpfc_printf_log(phba, KERN_INFO, LOG_INIT,
			"0455 Vital Product Data: x%x x%x x%x x%x\n",
			(uint32_t) vpd[0], (uint32_t) vpd[1], (uint32_t) vpd[2],
			(uint32_t) vpd[3]);
	while (!finished && (index < (len - 4))) {
		switch (vpd[index]) {
		case 0x82:
		case 0x91:
			index += 1;
			lenlo = vpd[index];
			index += 1;
			lenhi = vpd[index];
			index += 1;
			i = ((((unsigned short)lenhi) << 8) + lenlo);
			index += i;
			break;
		case 0x90:
			index += 1;
			lenlo = vpd[index];
			index += 1;
			lenhi = vpd[index];
			index += 1;
			Length = ((((unsigned short)lenhi) << 8) + lenlo);
			if (Length > len - index)
				Length = len - index;
			while (Length > 0) {
			/* Look for Serial Number */
			if ((vpd[index] == 'S') && (vpd[index+1] == 'N')) {
				index += 2;
				i = vpd[index];
				index += 1;
				j = 0;
				Length -= (3+i);
				while(i--) {
					phba->SerialNumber[j++] = vpd[index++];
					if (j == 31)
						break;
				}
				phba->SerialNumber[j] = 0;
				continue;
			}
			else if ((vpd[index] == 'V') && (vpd[index+1] == '1')) {
				phba->vpd_flag |= VPD_MODEL_DESC;
				index += 2;
				i = vpd[index];
				index += 1;
				j = 0;
				Length -= (3+i);
				while(i--) {
					phba->ModelDesc[j++] = vpd[index++];
					if (j == 255)
						break;
				}
				phba->ModelDesc[j] = 0;
				continue;
			}
			else if ((vpd[index] == 'V') && (vpd[index+1] == '2')) {
				phba->vpd_flag |= VPD_MODEL_NAME;
				index += 2;
				i = vpd[index];
				index += 1;
				j = 0;
				Length -= (3+i);
				while(i--) {
					phba->ModelName[j++] = vpd[index++];
					if (j == 79)
						break;
				}
				phba->ModelName[j] = 0;
				continue;
			}
			else if ((vpd[index] == 'V') && (vpd[index+1] == '3')) {
				phba->vpd_flag |= VPD_PROGRAM_TYPE;
				index += 2;
				i = vpd[index];
				index += 1;
				j = 0;
				Length -= (3+i);
				while(i--) {
					phba->ProgramType[j++] = vpd[index++];
					if (j == 255)
						break;
				}
				phba->ProgramType[j] = 0;
				continue;
			}
			else if ((vpd[index] == 'V') && (vpd[index+1] == '4')) {
				phba->vpd_flag |= VPD_PORT;
				index += 2;
				i = vpd[index];
				index += 1;
				j = 0;
				Length -= (3+i);
				while(i--) {
					if ((phba->sli_rev == LPFC_SLI_REV4) &&
					    (phba->sli4_hba.pport_name_sta ==
					     LPFC_SLI4_PPNAME_GET)) {
						j++;
						index++;
					} else
						phba->Port[j++] = vpd[index++];
					if (j == 19)
						break;
				}
				if ((phba->sli_rev != LPFC_SLI_REV4) ||
				    (phba->sli4_hba.pport_name_sta ==
				     LPFC_SLI4_PPNAME_NON))
					phba->Port[j] = 0;
				continue;
			}
			else {
				index += 2;
				i = vpd[index];
				index += 1;
				index += i;
				Length -= (3 + i);
			}
		}
		finished = 0;
		break;
		case 0x78:
			finished = 1;
			break;
		default:
			index ++;
			break;
		}
	}

	return(1);
}

/**
 * lpfc_get_hba_model_desc - Retrieve HBA device model name and description
 * @phba: pointer to lpfc hba data structure.
 * @mdp: pointer to the data structure to hold the derived model name.
 * @descp: pointer to the data structure to hold the derived description.
 *
 * This routine retrieves HBA's description based on its registered PCI device
 * ID. The @descp passed into this function points to an array of 256 chars. It
 * shall be returned with the model name, maximum speed, and the host bus type.
 * The @mdp passed into this function points to an array of 80 chars. When the
 * function returns, the @mdp will be filled with the model name.
 **/
static void
lpfc_get_hba_model_desc(struct lpfc_hba *phba, uint8_t *mdp, uint8_t *descp)
{
	lpfc_vpd_t *vp;
	uint16_t dev_id = phba->pcidev->device;
	int max_speed;
	int GE = 0;
	int oneConnect = 0; /* default is not a oneConnect */
	struct {
		char *name;
		char *bus;
		char *function;
	} m = {"<Unknown>", "", ""};

	if (mdp && mdp[0] != '\0'
		&& descp && descp[0] != '\0')
		return;

	if (phba->lmt & LMT_16Gb)
		max_speed = 16;
	else if (phba->lmt & LMT_10Gb)
		max_speed = 10;
	else if (phba->lmt & LMT_8Gb)
		max_speed = 8;
	else if (phba->lmt & LMT_4Gb)
		max_speed = 4;
	else if (phba->lmt & LMT_2Gb)
		max_speed = 2;
	else if (phba->lmt & LMT_1Gb)
		max_speed = 1;
	else
		max_speed = 0;

	vp = &phba->vpd;

	switch (dev_id) {
	case PCI_DEVICE_ID_FIREFLY:
		m = (typeof(m)){"LP6000", "PCI",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_SUPERFLY:
		if (vp->rev.biuRev >= 1 && vp->rev.biuRev <= 3)
			m = (typeof(m)){"LP7000", "PCI", ""};
		else
			m = (typeof(m)){"LP7000E", "PCI", ""};
		m.function = "Obsolete, Unsupported Fibre Channel Adapter";
		break;
	case PCI_DEVICE_ID_DRAGONFLY:
		m = (typeof(m)){"LP8000", "PCI",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_CENTAUR:
		if (FC_JEDEC_ID(vp->rev.biuRev) == CENTAUR_2G_JEDEC_ID)
			m = (typeof(m)){"LP9002", "PCI", ""};
		else
			m = (typeof(m)){"LP9000", "PCI", ""};
		m.function = "Obsolete, Unsupported Fibre Channel Adapter";
		break;
	case PCI_DEVICE_ID_RFLY:
		m = (typeof(m)){"LP952", "PCI",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_PEGASUS:
		m = (typeof(m)){"LP9802", "PCI-X",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_THOR:
		m = (typeof(m)){"LP10000", "PCI-X",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_VIPER:
		m = (typeof(m)){"LPX1000",  "PCI-X",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_PFLY:
		m = (typeof(m)){"LP982", "PCI-X",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_TFLY:
		m = (typeof(m)){"LP1050", "PCI-X",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_HELIOS:
		m = (typeof(m)){"LP11000", "PCI-X2",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_HELIOS_SCSP:
		m = (typeof(m)){"LP11000-SP", "PCI-X2",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_HELIOS_DCSP:
		m = (typeof(m)){"LP11002-SP",  "PCI-X2",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_NEPTUNE:
		m = (typeof(m)){"LPe1000", "PCIe",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_NEPTUNE_SCSP:
		m = (typeof(m)){"LPe1000-SP", "PCIe",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_NEPTUNE_DCSP:
		m = (typeof(m)){"LPe1002-SP", "PCIe",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_BMID:
		m = (typeof(m)){"LP1150", "PCI-X2", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_BSMB:
		m = (typeof(m)){"LP111", "PCI-X2",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_ZEPHYR:
		m = (typeof(m)){"LPe11000", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_ZEPHYR_SCSP:
		m = (typeof(m)){"LPe11000", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_ZEPHYR_DCSP:
		m = (typeof(m)){"LP2105", "PCIe", "FCoE Adapter"};
		GE = 1;
		break;
	case PCI_DEVICE_ID_ZMID:
		m = (typeof(m)){"LPe1150", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_ZSMB:
		m = (typeof(m)){"LPe111", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_LP101:
		m = (typeof(m)){"LP101", "PCI-X",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_LP10000S:
		m = (typeof(m)){"LP10000-S", "PCI",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_LP11000S:
		m = (typeof(m)){"LP11000-S", "PCI-X2",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_LPE11000S:
		m = (typeof(m)){"LPe11000-S", "PCIe",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_SAT:
		m = (typeof(m)){"LPe12000", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_SAT_MID:
		m = (typeof(m)){"LPe1250", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_SAT_SMB:
		m = (typeof(m)){"LPe121", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_SAT_DCSP:
		m = (typeof(m)){"LPe12002-SP", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_SAT_SCSP:
		m = (typeof(m)){"LPe12000-SP", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_SAT_S:
		m = (typeof(m)){"LPe12000-S", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_HORNET:
		m = (typeof(m)){"LP21000", "PCIe",
				"Obsolete, Unsupported FCoE Adapter"};
		GE = 1;
		break;
	case PCI_DEVICE_ID_PROTEUS_VF:
		m = (typeof(m)){"LPev12000", "PCIe IOV",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_PROTEUS_PF:
		m = (typeof(m)){"LPev12000", "PCIe IOV",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_PROTEUS_S:
		m = (typeof(m)){"LPemv12002-S", "PCIe IOV",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_TIGERSHARK:
		oneConnect = 1;
		m = (typeof(m)){"OCe10100", "PCIe", "FCoE"};
		break;
	case PCI_DEVICE_ID_TOMCAT:
		oneConnect = 1;
		m = (typeof(m)){"OCe11100", "PCIe", "FCoE"};
		break;
	case PCI_DEVICE_ID_FALCON:
		m = (typeof(m)){"LPSe12002-ML1-E", "PCIe",
				"EmulexSecure Fibre"};
		break;
	case PCI_DEVICE_ID_BALIUS:
		m = (typeof(m)){"LPVe12002", "PCIe Shared I/O",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_LANCER_FC:
		m = (typeof(m)){"LPe16000", "PCIe", "Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_LANCER_FC_VF:
		m = (typeof(m)){"LPe16000", "PCIe",
				"Obsolete, Unsupported Fibre Channel Adapter"};
		break;
	case PCI_DEVICE_ID_LANCER_FCOE:
		oneConnect = 1;
		m = (typeof(m)){"OCe15100", "PCIe", "FCoE"};
		break;
	case PCI_DEVICE_ID_LANCER_FCOE_VF:
		oneConnect = 1;
		m = (typeof(m)){"OCe15100", "PCIe",
				"Obsolete, Unsupported FCoE"};
		break;
	case PCI_DEVICE_ID_SKYHAWK:
	case PCI_DEVICE_ID_SKYHAWK_VF:
		oneConnect = 1;
		m = (typeof(m)){"OCe14000", "PCIe", "FCoE"};
		break;
	default:
		m = (typeof(m)){"Unknown", "", ""};
		break;
	}

	if (mdp && mdp[0] == '\0')
		snprintf(mdp, 79,"%s", m.name);
	/*
	 * oneConnect hba requires special processing, they are all initiators
	 * and we put the port number on the end
	 */
	if (descp && descp[0] == '\0') {
		if (oneConnect)
			snprintf(descp, 255,
				"Emulex OneConnect %s, %s Initiator %s",
				m.name, m.function,
				phba->Port);
		else if (max_speed == 0)
			snprintf(descp, 255,
				"Emulex %s %s %s ",
				m.name, m.bus, m.function);
		else
			snprintf(descp, 255,
				"Emulex %s %d%s %s %s",
				m.name, max_speed, (GE) ? "GE" : "Gb",
				m.bus, m.function);
	}
}

/**
 * lpfc_post_buffer - Post IOCB(s) with DMA buffer descriptor(s) to a IOCB ring
 * @phba: pointer to lpfc hba data structure.
 * @pring: pointer to a IOCB ring.
 * @cnt: the number of IOCBs to be posted to the IOCB ring.
 *
 * This routine posts a given number of IOCBs with the associated DMA buffer
 * descriptors specified by the cnt argument to the given IOCB ring.
 *
 * Return codes
 *   The number of IOCBs NOT able to be posted to the IOCB ring.
 **/
int
lpfc_post_buffer(struct lpfc_hba *phba, struct lpfc_sli_ring *pring, int cnt)
{
	IOCB_t *icmd;
	struct lpfc_iocbq *iocb;
	struct lpfc_dmabuf *mp1, *mp2;

	cnt += pring->missbufcnt;

	/* While there are buffers to post */
	while (cnt > 0) {
		/* Allocate buffer for  command iocb */
		iocb = lpfc_sli_get_iocbq(phba);
		if (iocb == NULL) {
			pring->missbufcnt = cnt;
			return cnt;
		}
		icmd = &iocb->iocb;

		/* 2 buffers can be posted per command */
		/* Allocate buffer to post */
		mp1 = kmalloc(sizeof (struct lpfc_dmabuf), GFP_KERNEL);
		if (mp1)
		    mp1->virt = lpfc_mbuf_alloc(phba, MEM_PRI, &mp1->phys);
		if (!mp1 || !mp1->virt) {
			kfree(mp1);
			lpfc_sli_release_iocbq(phba, iocb);
			pring->missbufcnt = cnt;
			return cnt;
		}

		INIT_LIST_HEAD(&mp1->list);
		/* Allocate buffer to post */
		if (cnt > 1) {
			mp2 = kmalloc(sizeof (struct lpfc_dmabuf), GFP_KERNEL);
			if (mp2)
				mp2->virt = lpfc_mbuf_alloc(phba, MEM_PRI,
							    &mp2->phys);
			if (!mp2 || !mp2->virt) {
				kfree(mp2);
				lpfc_mbuf_free(phba, mp1->virt, mp1->phys);
				kfree(mp1);
				lpfc_sli_release_iocbq(phba, iocb);
				pring->missbufcnt = cnt;
				return cnt;
			}

			INIT_LIST_HEAD(&mp2->list);
		} else {
			mp2 = NULL;
		}

		icmd->un.cont64[0].addrHigh = putPaddrHigh(mp1->phys);
		icmd->un.cont64[0].addrLow = putPaddrLow(mp1->phys);
		icmd->un.cont64[0].tus.f.bdeSize = FCELSSIZE;
		icmd->ulpBdeCount = 1;
		cnt--;
		if (mp2) {
			icmd->un.cont64[1].addrHigh = putPaddrHigh(mp2->phys);
			icmd->un.cont64[1].addrLow = putPaddrLow(mp2->phys);
			icmd->un.cont64[1].tus.f.bdeSize = FCELSSIZE;
			cnt--;
			icmd->ulpBdeCount = 2;
		}

		icmd->ulpCommand = CMD_QUE_RING_BUF64_CN;
		icmd->ulpLe = 1;

		if (lpfc_sli_issue_iocb(phba, pring->ringno, iocb, 0) ==
		    IOCB_ERROR) {
			lpfc_mbuf_free(phba, mp1->virt, mp1->phys);
			kfree(mp1);
			cnt++;
			if (mp2) {
				lpfc_mbuf_free(phba, mp2->virt, mp2->phys);
				kfree(mp2);
				cnt++;
			}
			lpfc_sli_release_iocbq(phba, iocb);
			pring->missbufcnt = cnt;
			return cnt;
		}
		lpfc_sli_ringpostbuf_put(phba, pring, mp1);
		if (mp2)
			lpfc_sli_ringpostbuf_put(phba, pring, mp2);
	}
	pring->missbufcnt = 0;
	return 0;
}

/**
 * lpfc_post_rcv_buf - Post the initial receive IOCB buffers to ELS ring
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine posts initial receive IOCB buffers to the ELS ring. The
 * current number of initial IOCB buffers specified by LPFC_BUF_RING0 is
 * set to 64 IOCBs.
 *
 * Return codes
 *   0 - success (currently always success)
 **/
static int
lpfc_post_rcv_buf(struct lpfc_hba *phba)
{
	struct lpfc_sli *psli = &phba->sli;

	/* Ring 0, ELS / CT buffers */
	lpfc_post_buffer(phba, &psli->ring[LPFC_ELS_RING], LPFC_BUF_RING0);
	/* Ring 2 - FCP no buffers needed */

	return 0;
}

#define S(N,V) (((V)<<(N))|((V)>>(32-(N))))

/**
 * lpfc_sha_init - Set up initial array of hash table entries
 * @HashResultPointer: pointer to an array as hash table.
 *
 * This routine sets up the initial values to the array of hash table entries
 * for the LC HBAs.
 **/
static void
lpfc_sha_init(uint32_t * HashResultPointer)
{
	HashResultPointer[0] = 0x67452301;
	HashResultPointer[1] = 0xEFCDAB89;
	HashResultPointer[2] = 0x98BADCFE;
	HashResultPointer[3] = 0x10325476;
	HashResultPointer[4] = 0xC3D2E1F0;
}

/**
 * lpfc_sha_iterate - Iterate initial hash table with the working hash table
 * @HashResultPointer: pointer to an initial/result hash table.
 * @HashWorkingPointer: pointer to an working hash table.
 *
 * This routine iterates an initial hash table pointed by @HashResultPointer
 * with the values from the working hash table pointeed by @HashWorkingPointer.
 * The results are putting back to the initial hash table, returned through
 * the @HashResultPointer as the result hash table.
 **/
static void
lpfc_sha_iterate(uint32_t * HashResultPointer, uint32_t * HashWorkingPointer)
{
	int t;
	uint32_t TEMP;
	uint32_t A, B, C, D, E;
	t = 16;
	do {
		HashWorkingPointer[t] =
		    S(1,
		      HashWorkingPointer[t - 3] ^ HashWorkingPointer[t -
								     8] ^
		      HashWorkingPointer[t - 14] ^ HashWorkingPointer[t - 16]);
	} while (++t <= 79);
	t = 0;
	A = HashResultPointer[0];
	B = HashResultPointer[1];
	C = HashResultPointer[2];
	D = HashResultPointer[3];
	E = HashResultPointer[4];

	do {
		if (t < 20) {
			TEMP = ((B & C) | ((~B) & D)) + 0x5A827999;
		} else if (t < 40) {
			TEMP = (B ^ C ^ D) + 0x6ED9EBA1;
		} else if (t < 60) {
			TEMP = ((B & C) | (B & D) | (C & D)) + 0x8F1BBCDC;
		} else {
			TEMP = (B ^ C ^ D) + 0xCA62C1D6;
		}
		TEMP += S(5, A) + E + HashWorkingPointer[t];
		E = D;
		D = C;
		C = S(30, B);
		B = A;
		A = TEMP;
	} while (++t <= 79);

	HashResultPointer[0] += A;
	HashResultPointer[1] += B;
	HashResultPointer[2] += C;
	HashResultPointer[3] += D;
	HashResultPointer[4] += E;

}

/**
 * lpfc_challenge_key - Create challenge key based on WWPN of the HBA
 * @RandomChallenge: pointer to the entry of host challenge random number array.
 * @HashWorking: pointer to the entry of the working hash array.
 *
 * This routine calculates the working hash array referred by @HashWorking
 * from the challenge random numbers associated with the host, referred by
 * @RandomChallenge. The result is put into the entry of the working hash
 * array and returned by reference through @HashWorking.
 **/
static void
lpfc_challenge_key(uint32_t * RandomChallenge, uint32_t * HashWorking)
{
	*HashWorking = (*RandomChallenge ^ *HashWorking);
}

/**
 * lpfc_hba_init - Perform special handling for LC HBA initialization
 * @phba: pointer to lpfc hba data structure.
 * @hbainit: pointer to an array of unsigned 32-bit integers.
 *
 * This routine performs the special handling for LC HBA initialization.
 **/
void
lpfc_hba_init(struct lpfc_hba *phba, uint32_t *hbainit)
{
	int t;
	uint32_t *HashWorking;
	uint32_t *pwwnn = (uint32_t *) phba->wwnn;

	HashWorking = kcalloc(80, sizeof(uint32_t), GFP_KERNEL);
	if (!HashWorking)
		return;

	HashWorking[0] = HashWorking[78] = *pwwnn++;
	HashWorking[1] = HashWorking[79] = *pwwnn;

	for (t = 0; t < 7; t++)
		lpfc_challenge_key(phba->RandomData + t, HashWorking + t);

	lpfc_sha_init(hbainit);
	lpfc_sha_iterate(hbainit, HashWorking);
	kfree(HashWorking);
}

/**
 * lpfc_cleanup - Performs vport cleanups before deleting a vport
 * @vport: pointer to a virtual N_Port data structure.
 *
 * This routine performs the necessary cleanups before deleting the @vport.
 * It invokes the discovery state machine to perform necessary state
 * transitions and to release the ndlps associated with the @vport. Note,
 * the physical port is treated as @vport 0.
 **/
void
lpfc_cleanup(struct lpfc_vport *vport)
{
	struct lpfc_hba   *phba = vport->phba;
	struct lpfc_nodelist *ndlp, *next_ndlp;
	int i = 0;

	if (phba->link_state > LPFC_LINK_DOWN)
		lpfc_port_link_failure(vport);

	list_for_each_entry_safe(ndlp, next_ndlp, &vport->fc_nodes, nlp_listp) {
		if (!NLP_CHK_NODE_ACT(ndlp)) {
			ndlp = lpfc_enable_node(vport, ndlp,
						NLP_STE_UNUSED_NODE);
			if (!ndlp)
				continue;
			spin_lock_irq(&phba->ndlp_lock);
			NLP_SET_FREE_REQ(ndlp);
			spin_unlock_irq(&phba->ndlp_lock);
			/* Trigger the release of the ndlp memory */
			lpfc_nlp_put(ndlp);
			continue;
		}
		spin_lock_irq(&phba->ndlp_lock);
		if (NLP_CHK_FREE_REQ(ndlp)) {
			/* The ndlp should not be in memory free mode already */
			spin_unlock_irq(&phba->ndlp_lock);
			continue;
		} else
			/* Indicate request for freeing ndlp memory */
			NLP_SET_FREE_REQ(ndlp);
		spin_unlock_irq(&phba->ndlp_lock);

		if (vport->port_type != LPFC_PHYSICAL_PORT &&
		    ndlp->nlp_DID == Fabric_DID) {
			/* Just free up ndlp with Fabric_DID for vports */
			lpfc_nlp_put(ndlp);
			continue;
		}

		/* take care of nodes in unused state before the state
		 * machine taking action.
		 */
		if (ndlp->nlp_state == NLP_STE_UNUSED_NODE) {
			lpfc_nlp_put(ndlp);
			continue;
		}

		if (ndlp->nlp_type & NLP_FABRIC)
			lpfc_disc_state_machine(vport, ndlp, NULL,
					NLP_EVT_DEVICE_RECOVERY);

		lpfc_disc_state_machine(vport, ndlp, NULL,
					     NLP_EVT_DEVICE_RM);
	}

	/* At this point, ALL ndlp's should be gone
	 * because of the previous NLP_EVT_DEVICE_RM.
	 * Lets wait for this to happen, if needed.
	 */
	while (!list_empty(&vport->fc_nodes)) {
		if (i++ > 3000) {
			lpfc_printf_vlog(vport, KERN_ERR, LOG_DISCOVERY,
				"0233 Nodelist not empty\n");
			list_for_each_entry_safe(ndlp, next_ndlp,
						&vport->fc_nodes, nlp_listp) {
				lpfc_printf_vlog(ndlp->vport, KERN_ERR,
						LOG_NODE,
						"0282 did:x%x ndlp:x%p "
						"usgmap:x%x refcnt:%d\n",
						ndlp->nlp_DID, (void *)ndlp,
						ndlp->nlp_usg_map,
						atomic_read(
							&ndlp->kref.refcount));
			}
			break;
		}

		/* Wait for any activity on ndlps to settle */
		msleep(10);
	}
	lpfc_cleanup_vports_rrqs(vport, NULL);
}

/**
 * lpfc_stop_vport_timers - Stop all the timers associated with a vport
 * @vport: pointer to a virtual N_Port data structure.
 *
 * This routine stops all the timers associated with a @vport. This function
 * is invoked before disabling or deleting a @vport. Note that the physical
 * port is treated as @vport 0.
 **/
void
lpfc_stop_vport_timers(struct lpfc_vport *vport)
{
	del_timer_sync(&vport->els_tmofunc);
	del_timer_sync(&vport->fc_fdmitmo);
	del_timer_sync(&vport->delayed_disc_tmo);
	lpfc_can_disctmo(vport);
	return;
}

/**
 * __lpfc_sli4_stop_fcf_redisc_wait_timer - Stop FCF rediscovery wait timer
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine stops the SLI4 FCF rediscover wait timer if it's on. The
 * caller of this routine should already hold the host lock.
 **/
void
__lpfc_sli4_stop_fcf_redisc_wait_timer(struct lpfc_hba *phba)
{
	/* Clear pending FCF rediscovery wait flag */
	phba->fcf.fcf_flag &= ~FCF_REDISC_PEND;

	/* Now, try to stop the timer */
	del_timer(&phba->fcf.redisc_wait);
}

/**
 * lpfc_sli4_stop_fcf_redisc_wait_timer - Stop FCF rediscovery wait timer
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine stops the SLI4 FCF rediscover wait timer if it's on. It
 * checks whether the FCF rediscovery wait timer is pending with the host
 * lock held before proceeding with disabling the timer and clearing the
 * wait timer pendig flag.
 **/
void
lpfc_sli4_stop_fcf_redisc_wait_timer(struct lpfc_hba *phba)
{
	spin_lock_irq(&phba->hbalock);
	if (!(phba->fcf.fcf_flag & FCF_REDISC_PEND)) {
		/* FCF rediscovery timer already fired or stopped */
		spin_unlock_irq(&phba->hbalock);
		return;
	}
	__lpfc_sli4_stop_fcf_redisc_wait_timer(phba);
	/* Clear failover in progress flags */
	phba->fcf.fcf_flag &= ~(FCF_DEAD_DISC | FCF_ACVL_DISC);
	spin_unlock_irq(&phba->hbalock);
}

/**
 * lpfc_stop_hba_timers - Stop all the timers associated with an HBA
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine stops all the timers associated with a HBA. This function is
 * invoked before either putting a HBA offline or unloading the driver.
 **/
void
lpfc_stop_hba_timers(struct lpfc_hba *phba)
{
	lpfc_stop_vport_timers(phba->pport);
	del_timer_sync(&phba->sli.mbox_tmo);
	del_timer_sync(&phba->fabric_block_timer);
	del_timer_sync(&phba->eratt_poll);
	del_timer_sync(&phba->hb_tmofunc);
	if (phba->sli_rev == LPFC_SLI_REV4) {
		del_timer_sync(&phba->rrq_tmr);
		phba->hba_flag &= ~HBA_RRQ_ACTIVE;
	}
	phba->hb_outstanding = 0;

	switch (phba->pci_dev_grp) {
	case LPFC_PCI_DEV_LP:
		/* Stop any LightPulse device specific driver timers */
		del_timer_sync(&phba->fcp_poll_timer);
		break;
	case LPFC_PCI_DEV_OC:
		/* Stop any OneConnect device sepcific driver timers */
		lpfc_sli4_stop_fcf_redisc_wait_timer(phba);
		break;
	default:
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0297 Invalid device group (x%x)\n",
				phba->pci_dev_grp);
		break;
	}
	return;
}

/**
 * lpfc_block_mgmt_io - Mark a HBA's management interface as blocked
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine marks a HBA's management interface as blocked. Once the HBA's
 * management interface is marked as blocked, all the user space access to
 * the HBA, whether they are from sysfs interface or libdfc interface will
 * all be blocked. The HBA is set to block the management interface when the
 * driver prepares the HBA interface for online or offline.
 **/
static void
lpfc_block_mgmt_io(struct lpfc_hba *phba, int mbx_action)
{
	unsigned long iflag;
	uint8_t actcmd = MBX_HEARTBEAT;
	unsigned long timeout;

	spin_lock_irqsave(&phba->hbalock, iflag);
	phba->sli.sli_flag |= LPFC_BLOCK_MGMT_IO;
	spin_unlock_irqrestore(&phba->hbalock, iflag);
	if (mbx_action == LPFC_MBX_NO_WAIT)
		return;
	timeout = msecs_to_jiffies(LPFC_MBOX_TMO * 1000) + jiffies;
	spin_lock_irqsave(&phba->hbalock, iflag);
	if (phba->sli.mbox_active) {
		actcmd = phba->sli.mbox_active->u.mb.mbxCommand;
		/* Determine how long we might wait for the active mailbox
		 * command to be gracefully completed by firmware.
		 */
		timeout = msecs_to_jiffies(lpfc_mbox_tmo_val(phba,
				phba->sli.mbox_active) * 1000) + jiffies;
	}
	spin_unlock_irqrestore(&phba->hbalock, iflag);

	/* Wait for the outstnading mailbox command to complete */
	while (phba->sli.mbox_active) {
		/* Check active mailbox complete status every 2ms */
		msleep(2);
		if (time_after(jiffies, timeout)) {
			lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
				"2813 Mgmt IO is Blocked %x "
				"- mbox cmd %x still active\n",
				phba->sli.sli_flag, actcmd);
			break;
		}
	}
}

/**
 * lpfc_sli4_node_prep - Assign RPIs for active nodes.
 * @phba: pointer to lpfc hba data structure.
 *
 * Allocate RPIs for all active remote nodes. This is needed whenever
 * an SLI4 adapter is reset and the driver is not unloading. Its purpose
 * is to fixup the temporary rpi assignments.
 **/
void
lpfc_sli4_node_prep(struct lpfc_hba *phba)
{
	struct lpfc_nodelist  *ndlp, *next_ndlp;
	struct lpfc_vport **vports;
	int i;

	if (phba->sli_rev != LPFC_SLI_REV4)
		return;

	vports = lpfc_create_vport_work_array(phba);
	if (vports != NULL) {
		for (i = 0; i <= phba->max_vports && vports[i] != NULL; i++) {
			if (vports[i]->load_flag & FC_UNLOADING)
				continue;

			list_for_each_entry_safe(ndlp, next_ndlp,
						 &vports[i]->fc_nodes,
						 nlp_listp) {
				if (NLP_CHK_NODE_ACT(ndlp)) {
					ndlp->nlp_rpi =
						lpfc_sli4_alloc_rpi(phba);
					lpfc_printf_vlog(ndlp->vport, KERN_INFO,
							 LOG_NODE,
							 "0009 rpi:%x DID:%x "
							 "flg:%x map:%x %p\n",
							 ndlp->nlp_rpi,
							 ndlp->nlp_DID,
							 ndlp->nlp_flag,
							 ndlp->nlp_usg_map,
							 ndlp);
				}
			}
		}
	}
	lpfc_destroy_vport_work_array(phba, vports);
}

/**
 * lpfc_online - Initialize and bring a HBA online
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine initializes the HBA and brings a HBA online. During this
 * process, the management interface is blocked to prevent user space access
 * to the HBA interfering with the driver initialization.
 *
 * Return codes
 *   0 - successful
 *   1 - failed
 **/
int
lpfc_online(struct lpfc_hba *phba)
{
	struct lpfc_vport *vport;
	struct lpfc_vport **vports;
	int i;
	bool vpis_cleared = false;

	if (!phba)
		return 0;
	vport = phba->pport;

	if (!(vport->fc_flag & FC_OFFLINE_MODE))
		return 0;

	lpfc_printf_log(phba, KERN_WARNING, LOG_INIT,
			"0458 Bring Adapter online\n");

	lpfc_block_mgmt_io(phba, LPFC_MBX_WAIT);

	if (!lpfc_sli_queue_setup(phba)) {
		lpfc_unblock_mgmt_io(phba);
		return 1;
	}

	if (phba->sli_rev == LPFC_SLI_REV4) {
		if (lpfc_sli4_hba_setup(phba)) { /* Initialize SLI4 HBA */
			lpfc_unblock_mgmt_io(phba);
			return 1;
		}
		spin_lock_irq(&phba->hbalock);
		if (!phba->sli4_hba.max_cfg_param.vpi_used)
			vpis_cleared = true;
		spin_unlock_irq(&phba->hbalock);
	} else {
		if (lpfc_sli_hba_setup(phba)) {	/* Initialize SLI2/SLI3 HBA */
			lpfc_unblock_mgmt_io(phba);
			return 1;
		}
	}

	vports = lpfc_create_vport_work_array(phba);
	if (vports != NULL)
		for (i = 0; i <= phba->max_vports && vports[i] != NULL; i++) {
			struct Scsi_Host *shost;
			shost = lpfc_shost_from_vport(vports[i]);
			spin_lock_irq(shost->host_lock);
			vports[i]->fc_flag &= ~FC_OFFLINE_MODE;
			if (phba->sli3_options & LPFC_SLI3_NPIV_ENABLED)
				vports[i]->fc_flag |= FC_VPORT_NEEDS_REG_VPI;
			if (phba->sli_rev == LPFC_SLI_REV4) {
				vports[i]->fc_flag |= FC_VPORT_NEEDS_INIT_VPI;
				if ((vpis_cleared) &&
				    (vports[i]->port_type !=
					LPFC_PHYSICAL_PORT))
					vports[i]->vpi = 0;
			}
			spin_unlock_irq(shost->host_lock);
		}
		lpfc_destroy_vport_work_array(phba, vports);

	lpfc_unblock_mgmt_io(phba);
	return 0;
}

/**
 * lpfc_unblock_mgmt_io - Mark a HBA's management interface to be not blocked
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine marks a HBA's management interface as not blocked. Once the
 * HBA's management interface is marked as not blocked, all the user space
 * access to the HBA, whether they are from sysfs interface or libdfc
 * interface will be allowed. The HBA is set to block the management interface
 * when the driver prepares the HBA interface for online or offline and then
 * set to unblock the management interface afterwards.
 **/
void
lpfc_unblock_mgmt_io(struct lpfc_hba * phba)
{
	unsigned long iflag;

	spin_lock_irqsave(&phba->hbalock, iflag);
	phba->sli.sli_flag &= ~LPFC_BLOCK_MGMT_IO;
	spin_unlock_irqrestore(&phba->hbalock, iflag);
}

/**
 * lpfc_offline_prep - Prepare a HBA to be brought offline
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked to prepare a HBA to be brought offline. It performs
 * unregistration login to all the nodes on all vports and flushes the mailbox
 * queue to make it ready to be brought offline.
 **/
void
lpfc_offline_prep(struct lpfc_hba *phba, int mbx_action)
{
	struct lpfc_vport *vport = phba->pport;
	struct lpfc_nodelist  *ndlp, *next_ndlp;
	struct lpfc_vport **vports;
	struct Scsi_Host *shost;
	int i;

	if (vport->fc_flag & FC_OFFLINE_MODE)
		return;

	lpfc_block_mgmt_io(phba, mbx_action);

	lpfc_linkdown(phba);

	/* Issue an unreg_login to all nodes on all vports */
	vports = lpfc_create_vport_work_array(phba);
	if (vports != NULL) {
		for (i = 0; i <= phba->max_vports && vports[i] != NULL; i++) {
			if (vports[i]->load_flag & FC_UNLOADING)
				continue;
			shost = lpfc_shost_from_vport(vports[i]);
			spin_lock_irq(shost->host_lock);
			vports[i]->vpi_state &= ~LPFC_VPI_REGISTERED;
			vports[i]->fc_flag |= FC_VPORT_NEEDS_REG_VPI;
			vports[i]->fc_flag &= ~FC_VFI_REGISTERED;
			spin_unlock_irq(shost->host_lock);

			shost =	lpfc_shost_from_vport(vports[i]);
			list_for_each_entry_safe(ndlp, next_ndlp,
						 &vports[i]->fc_nodes,
						 nlp_listp) {
				if (!NLP_CHK_NODE_ACT(ndlp))
					continue;
				if (ndlp->nlp_state == NLP_STE_UNUSED_NODE)
					continue;
				if (ndlp->nlp_type & NLP_FABRIC) {
					lpfc_disc_state_machine(vports[i], ndlp,
						NULL, NLP_EVT_DEVICE_RECOVERY);
					lpfc_disc_state_machine(vports[i], ndlp,
						NULL, NLP_EVT_DEVICE_RM);
				}
				spin_lock_irq(shost->host_lock);
				ndlp->nlp_flag &= ~NLP_NPR_ADISC;
				spin_unlock_irq(shost->host_lock);
				/*
				 * Whenever an SLI4 port goes offline, free the
				 * RPI. Get a new RPI when the adapter port
				 * comes back online.
				 */
				if (phba->sli_rev == LPFC_SLI_REV4) {
					lpfc_printf_vlog(ndlp->vport,
							 KERN_INFO, LOG_NODE,
							 "0011 lpfc_offline: "
							 "ndlp:x%p did %x "
							 "usgmap:x%x rpi:%x\n",
							 ndlp, ndlp->nlp_DID,
							 ndlp->nlp_usg_map,
							 ndlp->nlp_rpi);

					lpfc_sli4_free_rpi(phba, ndlp->nlp_rpi);
				}
				lpfc_unreg_rpi(vports[i], ndlp);
			}
		}
	}
	lpfc_destroy_vport_work_array(phba, vports);

	lpfc_sli_mbox_sys_shutdown(phba, mbx_action);
}

/**
 * lpfc_offline - Bring a HBA offline
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine actually brings a HBA offline. It stops all the timers
 * associated with the HBA, brings down the SLI layer, and eventually
 * marks the HBA as in offline state for the upper layer protocol.
 **/
void
lpfc_offline(struct lpfc_hba *phba)
{
	struct Scsi_Host  *shost;
	struct lpfc_vport **vports;
	int i;

	if (phba->pport->fc_flag & FC_OFFLINE_MODE)
		return;

	/* stop port and all timers associated with this hba */
	lpfc_stop_port(phba);
	vports = lpfc_create_vport_work_array(phba);
	if (vports != NULL)
		for (i = 0; i <= phba->max_vports && vports[i] != NULL; i++)
			lpfc_stop_vport_timers(vports[i]);
	lpfc_destroy_vport_work_array(phba, vports);
	lpfc_printf_log(phba, KERN_WARNING, LOG_INIT,
			"0460 Bring Adapter offline\n");
	/* Bring down the SLI Layer and cleanup.  The HBA is offline
	   now.  */
	lpfc_sli_hba_down(phba);
	spin_lock_irq(&phba->hbalock);
	phba->work_ha = 0;
	spin_unlock_irq(&phba->hbalock);
	vports = lpfc_create_vport_work_array(phba);
	if (vports != NULL)
		for (i = 0; i <= phba->max_vports && vports[i] != NULL; i++) {
			shost = lpfc_shost_from_vport(vports[i]);
			spin_lock_irq(shost->host_lock);
			vports[i]->work_port_events = 0;
			vports[i]->fc_flag |= FC_OFFLINE_MODE;
			spin_unlock_irq(shost->host_lock);
		}
	lpfc_destroy_vport_work_array(phba, vports);
}

/**
 * lpfc_scsi_free - Free all the SCSI buffers and IOCBs from driver lists
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is to free all the SCSI buffers and IOCBs from the driver
 * list back to kernel. It is called from lpfc_pci_remove_one to free
 * the internal resources before the device is removed from the system.
 **/
static void
lpfc_scsi_free(struct lpfc_hba *phba)
{
	struct lpfc_scsi_buf *sb, *sb_next;
	struct lpfc_iocbq *io, *io_next;

	spin_lock_irq(&phba->hbalock);

	/* Release all the lpfc_scsi_bufs maintained by this host. */

	spin_lock(&phba->scsi_buf_list_put_lock);
	list_for_each_entry_safe(sb, sb_next, &phba->lpfc_scsi_buf_list_put,
				 list) {
		list_del(&sb->list);
		pci_pool_free(phba->lpfc_scsi_dma_buf_pool, sb->data,
			      sb->dma_handle);
		kfree(sb);
		phba->total_scsi_bufs--;
	}
	spin_unlock(&phba->scsi_buf_list_put_lock);

	spin_lock(&phba->scsi_buf_list_get_lock);
	list_for_each_entry_safe(sb, sb_next, &phba->lpfc_scsi_buf_list_get,
				 list) {
		list_del(&sb->list);
		pci_pool_free(phba->lpfc_scsi_dma_buf_pool, sb->data,
			      sb->dma_handle);
		kfree(sb);
		phba->total_scsi_bufs--;
	}
	spin_unlock(&phba->scsi_buf_list_get_lock);

	/* Release all the lpfc_iocbq entries maintained by this host. */
	list_for_each_entry_safe(io, io_next, &phba->lpfc_iocb_list, list) {
		list_del(&io->list);
		kfree(io);
		phba->total_iocbq_bufs--;
	}

	spin_unlock_irq(&phba->hbalock);
}

/**
 * lpfc_sli4_xri_sgl_update - update xri-sgl sizing and mapping
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine first calculates the sizes of the current els and allocated
 * scsi sgl lists, and then goes through all sgls to updates the physical
 * XRIs assigned due to port function reset. During port initialization, the
 * current els and allocated scsi sgl lists are 0s.
 *
 * Return codes
 *   0 - successful (for now, it always returns 0)
 **/
int
lpfc_sli4_xri_sgl_update(struct lpfc_hba *phba)
{
	struct lpfc_sglq *sglq_entry = NULL, *sglq_entry_next = NULL;
	struct lpfc_scsi_buf *psb = NULL, *psb_next = NULL;
	uint16_t i, lxri, xri_cnt, els_xri_cnt, scsi_xri_cnt;
	LIST_HEAD(els_sgl_list);
	LIST_HEAD(scsi_sgl_list);
	int rc;
	struct lpfc_sli_ring *pring = &phba->sli.ring[LPFC_ELS_RING];

	/*
	 * update on pci function's els xri-sgl list
	 */
	els_xri_cnt = lpfc_sli4_get_els_iocb_cnt(phba);
	if (els_xri_cnt > phba->sli4_hba.els_xri_cnt) {
		/* els xri-sgl expanded */
		xri_cnt = els_xri_cnt - phba->sli4_hba.els_xri_cnt;
		lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
				"3157 ELS xri-sgl count increased from "
				"%d to %d\n", phba->sli4_hba.els_xri_cnt,
				els_xri_cnt);
		/* allocate the additional els sgls */
		for (i = 0; i < xri_cnt; i++) {
			sglq_entry = kzalloc(sizeof(struct lpfc_sglq),
					     GFP_KERNEL);
			if (sglq_entry == NULL) {
				lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
						"2562 Failure to allocate an "
						"ELS sgl entry:%d\n", i);
				rc = -ENOMEM;
				goto out_free_mem;
			}
			sglq_entry->buff_type = GEN_BUFF_TYPE;
			sglq_entry->virt = lpfc_mbuf_alloc(phba, 0,
							   &sglq_entry->phys);
			if (sglq_entry->virt == NULL) {
				kfree(sglq_entry);
				lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
						"2563 Failure to allocate an "
						"ELS mbuf:%d\n", i);
				rc = -ENOMEM;
				goto out_free_mem;
			}
			sglq_entry->sgl = sglq_entry->virt;
			memset(sglq_entry->sgl, 0, LPFC_BPL_SIZE);
			sglq_entry->state = SGL_FREED;
			list_add_tail(&sglq_entry->list, &els_sgl_list);
		}
		spin_lock_irq(&phba->hbalock);
		spin_lock(&pring->ring_lock);
		list_splice_init(&els_sgl_list, &phba->sli4_hba.lpfc_sgl_list);
		spin_unlock(&pring->ring_lock);
		spin_unlock_irq(&phba->hbalock);
	} else if (els_xri_cnt < phba->sli4_hba.els_xri_cnt) {
		/* els xri-sgl shrinked */
		xri_cnt = phba->sli4_hba.els_xri_cnt - els_xri_cnt;
		lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
				"3158 ELS xri-sgl count decreased from "
				"%d to %d\n", phba->sli4_hba.els_xri_cnt,
				els_xri_cnt);
		spin_lock_irq(&phba->hbalock);
		spin_lock(&pring->ring_lock);
		list_splice_init(&phba->sli4_hba.lpfc_sgl_list, &els_sgl_list);
		spin_unlock(&pring->ring_lock);
		spin_unlock_irq(&phba->hbalock);
		/* release extra els sgls from list */
		for (i = 0; i < xri_cnt; i++) {
			list_remove_head(&els_sgl_list,
					 sglq_entry, struct lpfc_sglq, list);
			if (sglq_entry) {
				lpfc_mbuf_free(phba, sglq_entry->virt,
					       sglq_entry->phys);
				kfree(sglq_entry);
			}
		}
		spin_lock_irq(&phba->hbalock);
		spin_lock(&pring->ring_lock);
		list_splice_init(&els_sgl_list, &phba->sli4_hba.lpfc_sgl_list);
		spin_unlock(&pring->ring_lock);
		spin_unlock_irq(&phba->hbalock);
	} else
		lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
				"3163 ELS xri-sgl count unchanged: %d\n",
				els_xri_cnt);
	phba->sli4_hba.els_xri_cnt = els_xri_cnt;

	/* update xris to els sgls on the list */
	sglq_entry = NULL;
	sglq_entry_next = NULL;
	list_for_each_entry_safe(sglq_entry, sglq_entry_next,
				 &phba->sli4_hba.lpfc_sgl_list, list) {
		lxri = lpfc_sli4_next_xritag(phba);
		if (lxri == NO_XRI) {
			lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
					"2400 Failed to allocate xri for "
					"ELS sgl\n");
			rc = -ENOMEM;
			goto out_free_mem;
		}
		sglq_entry->sli4_lxritag = lxri;
		sglq_entry->sli4_xritag = phba->sli4_hba.xri_ids[lxri];
	}

	/*
	 * update on pci function's allocated scsi xri-sgl list
	 */
	phba->total_scsi_bufs = 0;

	/* maximum number of xris available for scsi buffers */
	phba->sli4_hba.scsi_xri_max = phba->sli4_hba.max_cfg_param.max_xri -
				      els_xri_cnt;

	lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
			"2401 Current allocated SCSI xri-sgl count:%d, "
			"maximum  SCSI xri count:%d\n",
			phba->sli4_hba.scsi_xri_cnt,
			phba->sli4_hba.scsi_xri_max);

	spin_lock_irq(&phba->scsi_buf_list_get_lock);
	spin_lock(&phba->scsi_buf_list_put_lock);
	list_splice_init(&phba->lpfc_scsi_buf_list_get, &scsi_sgl_list);
	list_splice(&phba->lpfc_scsi_buf_list_put, &scsi_sgl_list);
	spin_unlock(&phba->scsi_buf_list_put_lock);
	spin_unlock_irq(&phba->scsi_buf_list_get_lock);

	if (phba->sli4_hba.scsi_xri_cnt > phba->sli4_hba.scsi_xri_max) {
		/* max scsi xri shrinked below the allocated scsi buffers */
		scsi_xri_cnt = phba->sli4_hba.scsi_xri_cnt -
					phba->sli4_hba.scsi_xri_max;
		/* release the extra allocated scsi buffers */
		for (i = 0; i < scsi_xri_cnt; i++) {
			list_remove_head(&scsi_sgl_list, psb,
					 struct lpfc_scsi_buf, list);
			if (psb) {
				pci_pool_free(phba->lpfc_scsi_dma_buf_pool,
					      psb->data, psb->dma_handle);
				kfree(psb);
			}
		}
		spin_lock_irq(&phba->scsi_buf_list_get_lock);
		phba->sli4_hba.scsi_xri_cnt -= scsi_xri_cnt;
		spin_unlock_irq(&phba->scsi_buf_list_get_lock);
	}

	/* update xris associated to remaining allocated scsi buffers */
	psb = NULL;
	psb_next = NULL;
	list_for_each_entry_safe(psb, psb_next, &scsi_sgl_list, list) {
		lxri = lpfc_sli4_next_xritag(phba);
		if (lxri == NO_XRI) {
			lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
					"2560 Failed to allocate xri for "
					"scsi buffer\n");
			rc = -ENOMEM;
			goto out_free_mem;
		}
		psb->cur_iocbq.sli4_lxritag = lxri;
		psb->cur_iocbq.sli4_xritag = phba->sli4_hba.xri_ids[lxri];
	}
	spin_lock_irq(&phba->scsi_buf_list_get_lock);
	spin_lock(&phba->scsi_buf_list_put_lock);
	list_splice_init(&scsi_sgl_list, &phba->lpfc_scsi_buf_list_get);
	INIT_LIST_HEAD(&phba->lpfc_scsi_buf_list_put);
	spin_unlock(&phba->scsi_buf_list_put_lock);
	spin_unlock_irq(&phba->scsi_buf_list_get_lock);

	return 0;

out_free_mem:
	lpfc_free_els_sgl_list(phba);
	lpfc_scsi_free(phba);
	return rc;
}

/**
 * lpfc_create_port - Create an FC port
 * @phba: pointer to lpfc hba data structure.
 * @instance: a unique integer ID to this FC port.
 * @dev: pointer to the device data structure.
 *
 * This routine creates a FC port for the upper layer protocol. The FC port
 * can be created on top of either a physical port or a virtual port provided
 * by the HBA. This routine also allocates a SCSI host data structure (shost)
 * and associates the FC port created before adding the shost into the SCSI
 * layer.
 *
 * Return codes
 *   @vport - pointer to the virtual N_Port data structure.
 *   NULL - port create failed.
 **/
struct lpfc_vport *
lpfc_create_port(struct lpfc_hba *phba, int instance, struct device *dev)
{
	struct lpfc_vport *vport;
	struct Scsi_Host  *shost;
	int error = 0;

	if (dev != &phba->pcidev->dev) {
		shost = scsi_host_alloc(&lpfc_vport_template,
					sizeof(struct lpfc_vport));
	} else {
		if (phba->sli_rev == LPFC_SLI_REV4)
			shost = scsi_host_alloc(&lpfc_template,
					sizeof(struct lpfc_vport));
		else
			shost = scsi_host_alloc(&lpfc_template_s3,
					sizeof(struct lpfc_vport));
	}
	if (!shost)
		goto out;

	vport = (struct lpfc_vport *) shost->hostdata;
	vport->phba = phba;
	vport->load_flag |= FC_LOADING;
	vport->fc_flag |= FC_VPORT_NEEDS_REG_VPI;
	vport->fc_rscn_flush = 0;

	lpfc_get_vport_cfgparam(vport);
	shost->unique_id = instance;
	shost->max_id = LPFC_MAX_TARGET;
	shost->max_lun = vport->cfg_max_luns;
	shost->this_id = -1;
	shost->max_cmd_len = 16;
	if (phba->sli_rev == LPFC_SLI_REV4) {
		shost->dma_boundary =
			phba->sli4_hba.pc_sli4_params.sge_supp_len-1;
		shost->sg_tablesize = phba->cfg_sg_seg_cnt;
	}

	/*
	 * Set initial can_queue value since 0 is no longer supported and
	 * scsi_add_host will fail. This will be adjusted later based on the
	 * max xri value determined in hba setup.
	 */
	shost->can_queue = phba->cfg_hba_queue_depth - 10;
	if (dev != &phba->pcidev->dev) {
		shost->transportt = lpfc_vport_transport_template;
		vport->port_type = LPFC_NPIV_PORT;
	} else {
		shost->transportt = lpfc_transport_template;
		vport->port_type = LPFC_PHYSICAL_PORT;
	}

	/* Initialize all internally managed lists. */
	INIT_LIST_HEAD(&vport->fc_nodes);
	INIT_LIST_HEAD(&vport->rcv_buffer_list);
	spin_lock_init(&vport->work_port_lock);

	init_timer(&vport->fc_disctmo);
	vport->fc_disctmo.function = lpfc_disc_timeout;
	vport->fc_disctmo.data = (unsigned long)vport;

	init_timer(&vport->fc_fdmitmo);
	vport->fc_fdmitmo.function = lpfc_fdmi_tmo;
	vport->fc_fdmitmo.data = (unsigned long)vport;

	init_timer(&vport->els_tmofunc);
	vport->els_tmofunc.function = lpfc_els_timeout;
	vport->els_tmofunc.data = (unsigned long)vport;

	init_timer(&vport->delayed_disc_tmo);
	vport->delayed_disc_tmo.function = lpfc_delayed_disc_tmo;
	vport->delayed_disc_tmo.data = (unsigned long)vport;

	error = scsi_add_host_with_dma(shost, dev, &phba->pcidev->dev);
	if (error)
		goto out_put_shost;

	spin_lock_irq(&phba->hbalock);
	list_add_tail(&vport->listentry, &phba->port_list);
	spin_unlock_irq(&phba->hbalock);
	return vport;

out_put_shost:
	scsi_host_put(shost);
out:
	return NULL;
}

/**
 * destroy_port -  destroy an FC port
 * @vport: pointer to an lpfc virtual N_Port data structure.
 *
 * This routine destroys a FC port from the upper layer protocol. All the
 * resources associated with the port are released.
 **/
void
destroy_port(struct lpfc_vport *vport)
{
	struct Scsi_Host *shost = lpfc_shost_from_vport(vport);
	struct lpfc_hba  *phba = vport->phba;

	lpfc_debugfs_terminate(vport);
	fc_remove_host(shost);
	scsi_remove_host(shost);

	spin_lock_irq(&phba->hbalock);
	list_del_init(&vport->listentry);
	spin_unlock_irq(&phba->hbalock);

	lpfc_cleanup(vport);
	return;
}

/**
 * lpfc_get_instance - Get a unique integer ID
 *
 * This routine allocates a unique integer ID from lpfc_hba_index pool. It
 * uses the kernel idr facility to perform the task.
 *
 * Return codes:
 *   instance - a unique integer ID allocated as the new instance.
 *   -1 - lpfc get instance failed.
 **/
int
lpfc_get_instance(void)
{
	int ret;

	ret = idr_alloc(&lpfc_hba_index, NULL, 0, 0, GFP_KERNEL);
	return ret < 0 ? -1 : ret;
}

/**
 * lpfc_scan_finished - method for SCSI layer to detect whether scan is done
 * @shost: pointer to SCSI host data structure.
 * @time: elapsed time of the scan in jiffies.
 *
 * This routine is called by the SCSI layer with a SCSI host to determine
 * whether the scan host is finished.
 *
 * Note: there is no scan_start function as adapter initialization will have
 * asynchronously kicked off the link initialization.
 *
 * Return codes
 *   0 - SCSI host scan is not over yet.
 *   1 - SCSI host scan is over.
 **/
int lpfc_scan_finished(struct Scsi_Host *shost, unsigned long time)
{
	struct lpfc_vport *vport = (struct lpfc_vport *) shost->hostdata;
	struct lpfc_hba   *phba = vport->phba;
	int stat = 0;

	spin_lock_irq(shost->host_lock);

	if (vport->load_flag & FC_UNLOADING) {
		stat = 1;
		goto finished;
	}
	if (time >= msecs_to_jiffies(30 * 1000)) {
		lpfc_printf_log(phba, KERN_INFO, LOG_INIT,
				"0461 Scanning longer than 30 "
				"seconds.  Continuing initialization\n");
		stat = 1;
		goto finished;
	}
	if (time >= msecs_to_jiffies(15 * 1000) &&
	    phba->link_state <= LPFC_LINK_DOWN) {
		lpfc_printf_log(phba, KERN_INFO, LOG_INIT,
				"0465 Link down longer than 15 "
				"seconds.  Continuing initialization\n");
		stat = 1;
		goto finished;
	}

	if (vport->port_state != LPFC_VPORT_READY)
		goto finished;
	if (vport->num_disc_nodes || vport->fc_prli_sent)
		goto finished;
	if (vport->fc_map_cnt == 0 && time < msecs_to_jiffies(2 * 1000))
		goto finished;
	if ((phba->sli.sli_flag & LPFC_SLI_MBOX_ACTIVE) != 0)
		goto finished;

	stat = 1;

finished:
	spin_unlock_irq(shost->host_lock);
	return stat;
}

/**
 * lpfc_host_attrib_init - Initialize SCSI host attributes on a FC port
 * @shost: pointer to SCSI host data structure.
 *
 * This routine initializes a given SCSI host attributes on a FC port. The
 * SCSI host can be either on top of a physical port or a virtual port.
 **/
void lpfc_host_attrib_init(struct Scsi_Host *shost)
{
	struct lpfc_vport *vport = (struct lpfc_vport *) shost->hostdata;
	struct lpfc_hba   *phba = vport->phba;
	/*
	 * Set fixed host attributes.  Must done after lpfc_sli_hba_setup().
	 */

	fc_host_node_name(shost) = wwn_to_u64(vport->fc_nodename.u.wwn);
	fc_host_port_name(shost) = wwn_to_u64(vport->fc_portname.u.wwn);
	fc_host_supported_classes(shost) = FC_COS_CLASS3;

	memset(fc_host_supported_fc4s(shost), 0,
	       sizeof(fc_host_supported_fc4s(shost)));
	fc_host_supported_fc4s(shost)[2] = 1;
	fc_host_supported_fc4s(shost)[7] = 1;

	lpfc_vport_symbolic_node_name(vport, fc_host_symbolic_name(shost),
				 sizeof fc_host_symbolic_name(shost));

	fc_host_supported_speeds(shost) = 0;
	if (phba->lmt & LMT_16Gb)
		fc_host_supported_speeds(shost) |= FC_PORTSPEED_16GBIT;
	if (phba->lmt & LMT_10Gb)
		fc_host_supported_speeds(shost) |= FC_PORTSPEED_10GBIT;
	if (phba->lmt & LMT_8Gb)
		fc_host_supported_speeds(shost) |= FC_PORTSPEED_8GBIT;
	if (phba->lmt & LMT_4Gb)
		fc_host_supported_speeds(shost) |= FC_PORTSPEED_4GBIT;
	if (phba->lmt & LMT_2Gb)
		fc_host_supported_speeds(shost) |= FC_PORTSPEED_2GBIT;
	if (phba->lmt & LMT_1Gb)
		fc_host_supported_speeds(shost) |= FC_PORTSPEED_1GBIT;

	fc_host_maxframe_size(shost) =
		(((uint32_t) vport->fc_sparam.cmn.bbRcvSizeMsb & 0x0F) << 8) |
		(uint32_t) vport->fc_sparam.cmn.bbRcvSizeLsb;

	fc_host_dev_loss_tmo(shost) = vport->cfg_devloss_tmo;

	/* This value is also unchanging */
	memset(fc_host_active_fc4s(shost), 0,
	       sizeof(fc_host_active_fc4s(shost)));
	fc_host_active_fc4s(shost)[2] = 1;
	fc_host_active_fc4s(shost)[7] = 1;

	fc_host_max_npiv_vports(shost) = phba->max_vpi;
	spin_lock_irq(shost->host_lock);
	vport->load_flag &= ~FC_LOADING;
	spin_unlock_irq(shost->host_lock);
}

/**
 * lpfc_stop_port_s3 - Stop SLI3 device port
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked to stop an SLI3 device port, it stops the device
 * from generating interrupts and stops the device driver's timers for the
 * device.
 **/
static void
lpfc_stop_port_s3(struct lpfc_hba *phba)
{
	/* Clear all interrupt enable conditions */
	writel(0, phba->HCregaddr);
	readl(phba->HCregaddr); /* flush */
	/* Clear all pending interrupts */
	writel(0xffffffff, phba->HAregaddr);
	readl(phba->HAregaddr); /* flush */

	/* Reset some HBA SLI setup states */
	lpfc_stop_hba_timers(phba);
	phba->pport->work_port_events = 0;
}

/**
 * lpfc_stop_port_s4 - Stop SLI4 device port
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked to stop an SLI4 device port, it stops the device
 * from generating interrupts and stops the device driver's timers for the
 * device.
 **/
static void
lpfc_stop_port_s4(struct lpfc_hba *phba)
{
	/* Reset some HBA SLI4 setup states */
	lpfc_stop_hba_timers(phba);
	phba->pport->work_port_events = 0;
	phba->sli4_hba.intr_enable = 0;
}

/**
 * lpfc_stop_port - Wrapper function for stopping hba port
 * @phba: Pointer to HBA context object.
 *
 * This routine wraps the actual SLI3 or SLI4 hba stop port routine from
 * the API jump table function pointer from the lpfc_hba struct.
 **/
void
lpfc_stop_port(struct lpfc_hba *phba)
{
	phba->lpfc_stop_port(phba);
}

/**
 * lpfc_fcf_redisc_wait_start_timer - Start fcf rediscover wait timer
 * @phba: Pointer to hba for which this call is being executed.
 *
 * This routine starts the timer waiting for the FCF rediscovery to complete.
 **/
void
lpfc_fcf_redisc_wait_start_timer(struct lpfc_hba *phba)
{
	unsigned long fcf_redisc_wait_tmo =
		(jiffies + msecs_to_jiffies(LPFC_FCF_REDISCOVER_WAIT_TMO));
	/* Start fcf rediscovery wait period timer */
	mod_timer(&phba->fcf.redisc_wait, fcf_redisc_wait_tmo);
	spin_lock_irq(&phba->hbalock);
	/* Allow action to new fcf asynchronous event */
	phba->fcf.fcf_flag &= ~(FCF_AVAILABLE | FCF_SCAN_DONE);
	/* Mark the FCF rediscovery pending state */
	phba->fcf.fcf_flag |= FCF_REDISC_PEND;
	spin_unlock_irq(&phba->hbalock);
}

/**
 * lpfc_sli4_fcf_redisc_wait_tmo - FCF table rediscover wait timeout
 * @ptr: Map to lpfc_hba data structure pointer.
 *
 * This routine is invoked when waiting for FCF table rediscover has been
 * timed out. If new FCF record(s) has (have) been discovered during the
 * wait period, a new FCF event shall be added to the FCOE async event
 * list, and then worker thread shall be waked up for processing from the
 * worker thread context.
 **/
static void
lpfc_sli4_fcf_redisc_wait_tmo(unsigned long ptr)
{
	struct lpfc_hba *phba = (struct lpfc_hba *)ptr;

	/* Don't send FCF rediscovery event if timer cancelled */
	spin_lock_irq(&phba->hbalock);
	if (!(phba->fcf.fcf_flag & FCF_REDISC_PEND)) {
		spin_unlock_irq(&phba->hbalock);
		return;
	}
	/* Clear FCF rediscovery timer pending flag */
	phba->fcf.fcf_flag &= ~FCF_REDISC_PEND;
	/* FCF rediscovery event to worker thread */
	phba->fcf.fcf_flag |= FCF_REDISC_EVT;
	spin_unlock_irq(&phba->hbalock);
	lpfc_printf_log(phba, KERN_INFO, LOG_FIP,
			"2776 FCF rediscover quiescent timer expired\n");
	/* wake up worker thread */
	lpfc_worker_wake_up(phba);
}

/**
 * lpfc_sli4_parse_latt_fault - Parse sli4 link-attention link fault code
 * @phba: pointer to lpfc hba data structure.
 * @acqe_link: pointer to the async link completion queue entry.
 *
 * This routine is to parse the SLI4 link-attention link fault code and
 * translate it into the base driver's read link attention mailbox command
 * status.
 *
 * Return: Link-attention status in terms of base driver's coding.
 **/
static uint16_t
lpfc_sli4_parse_latt_fault(struct lpfc_hba *phba,
			   struct lpfc_acqe_link *acqe_link)
{
	uint16_t latt_fault;

	switch (bf_get(lpfc_acqe_link_fault, acqe_link)) {
	case LPFC_ASYNC_LINK_FAULT_NONE:
	case LPFC_ASYNC_LINK_FAULT_LOCAL:
	case LPFC_ASYNC_LINK_FAULT_REMOTE:
		latt_fault = 0;
		break;
	default:
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0398 Invalid link fault code: x%x\n",
				bf_get(lpfc_acqe_link_fault, acqe_link));
		latt_fault = MBXERR_ERROR;
		break;
	}
	return latt_fault;
}

/**
 * lpfc_sli4_parse_latt_type - Parse sli4 link attention type
 * @phba: pointer to lpfc hba data structure.
 * @acqe_link: pointer to the async link completion queue entry.
 *
 * This routine is to parse the SLI4 link attention type and translate it
 * into the base driver's link attention type coding.
 *
 * Return: Link attention type in terms of base driver's coding.
 **/
static uint8_t
lpfc_sli4_parse_latt_type(struct lpfc_hba *phba,
			  struct lpfc_acqe_link *acqe_link)
{
	uint8_t att_type;

	switch (bf_get(lpfc_acqe_link_status, acqe_link)) {
	case LPFC_ASYNC_LINK_STATUS_DOWN:
	case LPFC_ASYNC_LINK_STATUS_LOGICAL_DOWN:
		att_type = LPFC_ATT_LINK_DOWN;
		break;
	case LPFC_ASYNC_LINK_STATUS_UP:
		/* Ignore physical link up events - wait for logical link up */
		att_type = LPFC_ATT_RESERVED;
		break;
	case LPFC_ASYNC_LINK_STATUS_LOGICAL_UP:
		att_type = LPFC_ATT_LINK_UP;
		break;
	default:
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0399 Invalid link attention type: x%x\n",
				bf_get(lpfc_acqe_link_status, acqe_link));
		att_type = LPFC_ATT_RESERVED;
		break;
	}
	return att_type;
}

/**
 * lpfc_sli4_parse_latt_link_speed - Parse sli4 link-attention link speed
 * @phba: pointer to lpfc hba data structure.
 * @acqe_link: pointer to the async link completion queue entry.
 *
 * This routine is to parse the SLI4 link-attention link speed and translate
 * it into the base driver's link-attention link speed coding.
 *
 * Return: Link-attention link speed in terms of base driver's coding.
 **/
static uint8_t
lpfc_sli4_parse_latt_link_speed(struct lpfc_hba *phba,
				struct lpfc_acqe_link *acqe_link)
{
	uint8_t link_speed;

	switch (bf_get(lpfc_acqe_link_speed, acqe_link)) {
	case LPFC_ASYNC_LINK_SPEED_ZERO:
	case LPFC_ASYNC_LINK_SPEED_10MBPS:
	case LPFC_ASYNC_LINK_SPEED_100MBPS:
		link_speed = LPFC_LINK_SPEED_UNKNOWN;
		break;
	case LPFC_ASYNC_LINK_SPEED_1GBPS:
		link_speed = LPFC_LINK_SPEED_1GHZ;
		break;
	case LPFC_ASYNC_LINK_SPEED_10GBPS:
		link_speed = LPFC_LINK_SPEED_10GHZ;
		break;
	case LPFC_ASYNC_LINK_SPEED_20GBPS:
	case LPFC_ASYNC_LINK_SPEED_25GBPS:
	case LPFC_ASYNC_LINK_SPEED_40GBPS:
		link_speed = LPFC_LINK_SPEED_UNKNOWN;
		break;
	default:
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0483 Invalid link-attention link speed: x%x\n",
				bf_get(lpfc_acqe_link_speed, acqe_link));
		link_speed = LPFC_LINK_SPEED_UNKNOWN;
		break;
	}
	return link_speed;
}

/**
 * lpfc_sli_port_speed_get - Get sli3 link speed code to link speed
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is to get an SLI3 FC port's link speed in Mbps.
 *
 * Return: link speed in terms of Mbps.
 **/
uint32_t
lpfc_sli_port_speed_get(struct lpfc_hba *phba)
{
	uint32_t link_speed;

	if (!lpfc_is_link_up(phba))
		return 0;

	switch (phba->fc_linkspeed) {
	case LPFC_LINK_SPEED_1GHZ:
		link_speed = 1000;
		break;
	case LPFC_LINK_SPEED_2GHZ:
		link_speed = 2000;
		break;
	case LPFC_LINK_SPEED_4GHZ:
		link_speed = 4000;
		break;
	case LPFC_LINK_SPEED_8GHZ:
		link_speed = 8000;
		break;
	case LPFC_LINK_SPEED_10GHZ:
		link_speed = 10000;
		break;
	case LPFC_LINK_SPEED_16GHZ:
		link_speed = 16000;
		break;
	default:
		link_speed = 0;
	}
	return link_speed;
}

/**
 * lpfc_sli4_port_speed_parse - Parse async evt link speed code to link speed
 * @phba: pointer to lpfc hba data structure.
 * @evt_code: asynchronous event code.
 * @speed_code: asynchronous event link speed code.
 *
 * This routine is to parse the giving SLI4 async event link speed code into
 * value of Mbps for the link speed.
 *
 * Return: link speed in terms of Mbps.
 **/
static uint32_t
lpfc_sli4_port_speed_parse(struct lpfc_hba *phba, uint32_t evt_code,
			   uint8_t speed_code)
{
	uint32_t port_speed;

	switch (evt_code) {
	case LPFC_TRAILER_CODE_LINK:
		switch (speed_code) {
		case LPFC_ASYNC_LINK_SPEED_ZERO:
			port_speed = 0;
			break;
		case LPFC_ASYNC_LINK_SPEED_10MBPS:
			port_speed = 10;
			break;
		case LPFC_ASYNC_LINK_SPEED_100MBPS:
			port_speed = 100;
			break;
		case LPFC_ASYNC_LINK_SPEED_1GBPS:
			port_speed = 1000;
			break;
		case LPFC_ASYNC_LINK_SPEED_10GBPS:
			port_speed = 10000;
			break;
		case LPFC_ASYNC_LINK_SPEED_20GBPS:
			port_speed = 20000;
			break;
		case LPFC_ASYNC_LINK_SPEED_25GBPS:
			port_speed = 25000;
			break;
		case LPFC_ASYNC_LINK_SPEED_40GBPS:
			port_speed = 40000;
			break;
		default:
			port_speed = 0;
		}
		break;
	case LPFC_TRAILER_CODE_FC:
		switch (speed_code) {
		case LPFC_FC_LA_SPEED_UNKNOWN:
			port_speed = 0;
			break;
		case LPFC_FC_LA_SPEED_1G:
			port_speed = 1000;
			break;
		case LPFC_FC_LA_SPEED_2G:
			port_speed = 2000;
			break;
		case LPFC_FC_LA_SPEED_4G:
			port_speed = 4000;
			break;
		case LPFC_FC_LA_SPEED_8G:
			port_speed = 8000;
			break;
		case LPFC_FC_LA_SPEED_10G:
			port_speed = 10000;
			break;
		case LPFC_FC_LA_SPEED_16G:
			port_speed = 16000;
			break;
		default:
			port_speed = 0;
		}
		break;
	default:
		port_speed = 0;
	}
	return port_speed;
}

/**
 * lpfc_sli4_async_link_evt - Process the asynchronous FCoE link event
 * @phba: pointer to lpfc hba data structure.
 * @acqe_link: pointer to the async link completion queue entry.
 *
 * This routine is to handle the SLI4 asynchronous FCoE link event.
 **/
static void
lpfc_sli4_async_link_evt(struct lpfc_hba *phba,
			 struct lpfc_acqe_link *acqe_link)
{
	struct lpfc_dmabuf *mp;
	LPFC_MBOXQ_t *pmb;
	MAILBOX_t *mb;
	struct lpfc_mbx_read_top *la;
	uint8_t att_type;
	int rc;

	att_type = lpfc_sli4_parse_latt_type(phba, acqe_link);
	if (att_type != LPFC_ATT_LINK_DOWN && att_type != LPFC_ATT_LINK_UP)
		return;
	phba->fcoe_eventtag = acqe_link->event_tag;
	pmb = (LPFC_MBOXQ_t *)mempool_alloc(phba->mbox_mem_pool, GFP_KERNEL);
	if (!pmb) {
		lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
				"0395 The mboxq allocation failed\n");
		return;
	}
	mp = kmalloc(sizeof(struct lpfc_dmabuf), GFP_KERNEL);
	if (!mp) {
		lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
				"0396 The lpfc_dmabuf allocation failed\n");
		goto out_free_pmb;
	}
	mp->virt = lpfc_mbuf_alloc(phba, 0, &mp->phys);
	if (!mp->virt) {
		lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
				"0397 The mbuf allocation failed\n");
		goto out_free_dmabuf;
	}

	/* Cleanup any outstanding ELS commands */
	lpfc_els_flush_all_cmd(phba);

	/* Block ELS IOCBs until we have done process link event */
	phba->sli.ring[LPFC_ELS_RING].flag |= LPFC_STOP_IOCB_EVENT;

	/* Update link event statistics */
	phba->sli.slistat.link_event++;

	/* Create lpfc_handle_latt mailbox command from link ACQE */
	lpfc_read_topology(phba, pmb, mp);
	pmb->mbox_cmpl = lpfc_mbx_cmpl_read_topology;
	pmb->vport = phba->pport;

	/* Keep the link status for extra SLI4 state machine reference */
	phba->sli4_hba.link_state.speed =
			lpfc_sli4_port_speed_parse(phba, LPFC_TRAILER_CODE_LINK,
				bf_get(lpfc_acqe_link_speed, acqe_link));
	phba->sli4_hba.link_state.duplex =
				bf_get(lpfc_acqe_link_duplex, acqe_link);
	phba->sli4_hba.link_state.status =
				bf_get(lpfc_acqe_link_status, acqe_link);
	phba->sli4_hba.link_state.type =
				bf_get(lpfc_acqe_link_type, acqe_link);
	phba->sli4_hba.link_state.number =
				bf_get(lpfc_acqe_link_number, acqe_link);
	phba->sli4_hba.link_state.fault =
				bf_get(lpfc_acqe_link_fault, acqe_link);
	phba->sli4_hba.link_state.logical_speed =
			bf_get(lpfc_acqe_logical_link_speed, acqe_link) * 10;

	lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
			"2900 Async FC/FCoE Link event - Speed:%dGBit "
			"duplex:x%x LA Type:x%x Port Type:%d Port Number:%d "
			"Logical speed:%dMbps Fault:%d\n",
			phba->sli4_hba.link_state.speed,
			phba->sli4_hba.link_state.topology,
			phba->sli4_hba.link_state.status,
			phba->sli4_hba.link_state.type,
			phba->sli4_hba.link_state.number,
			phba->sli4_hba.link_state.logical_speed,
			phba->sli4_hba.link_state.fault);
	/*
	 * For FC Mode: issue the READ_TOPOLOGY mailbox command to fetch
	 * topology info. Note: Optional for non FC-AL ports.
	 */
	if (!(phba->hba_flag & HBA_FCOE_MODE)) {
		rc = lpfc_sli_issue_mbox(phba, pmb, MBX_NOWAIT);
		if (rc == MBX_NOT_FINISHED)
			goto out_free_dmabuf;
		return;
	}
	/*
	 * For FCoE Mode: fill in all the topology information we need and call
	 * the READ_TOPOLOGY completion routine to continue without actually
	 * sending the READ_TOPOLOGY mailbox command to the port.
	 */
	/* Parse and translate status field */
	mb = &pmb->u.mb;
	mb->mbxStatus = lpfc_sli4_parse_latt_fault(phba, acqe_link);

	/* Parse and translate link attention fields */
	la = (struct lpfc_mbx_read_top *) &pmb->u.mb.un.varReadTop;
	la->eventTag = acqe_link->event_tag;
	bf_set(lpfc_mbx_read_top_att_type, la, att_type);
	bf_set(lpfc_mbx_read_top_link_spd, la,
	       lpfc_sli4_parse_latt_link_speed(phba, acqe_link));

	/* Fake the the following irrelvant fields */
	bf_set(lpfc_mbx_read_top_topology, la, LPFC_TOPOLOGY_PT_PT);
	bf_set(lpfc_mbx_read_top_alpa_granted, la, 0);
	bf_set(lpfc_mbx_read_top_il, la, 0);
	bf_set(lpfc_mbx_read_top_pb, la, 0);
	bf_set(lpfc_mbx_read_top_fa, la, 0);
	bf_set(lpfc_mbx_read_top_mm, la, 0);

	/* Invoke the lpfc_handle_latt mailbox command callback function */
	lpfc_mbx_cmpl_read_topology(phba, pmb);

	return;

out_free_dmabuf:
	kfree(mp);
out_free_pmb:
	mempool_free(pmb, phba->mbox_mem_pool);
}

/**
 * lpfc_sli4_async_fc_evt - Process the asynchronous FC link event
 * @phba: pointer to lpfc hba data structure.
 * @acqe_fc: pointer to the async fc completion queue entry.
 *
 * This routine is to handle the SLI4 asynchronous FC event. It will simply log
 * that the event was received and then issue a read_topology mailbox command so
 * that the rest of the driver will treat it the same as SLI3.
 **/
static void
lpfc_sli4_async_fc_evt(struct lpfc_hba *phba, struct lpfc_acqe_fc_la *acqe_fc)
{
	struct lpfc_dmabuf *mp;
	LPFC_MBOXQ_t *pmb;
	int rc;

	if (bf_get(lpfc_trailer_type, acqe_fc) !=
	    LPFC_FC_LA_EVENT_TYPE_FC_LINK) {
		lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
				"2895 Non FC link Event detected.(%d)\n",
				bf_get(lpfc_trailer_type, acqe_fc));
		return;
	}
	/* Keep the link status for extra SLI4 state machine reference */
	phba->sli4_hba.link_state.speed =
			lpfc_sli4_port_speed_parse(phba, LPFC_TRAILER_CODE_FC,
				bf_get(lpfc_acqe_fc_la_speed, acqe_fc));
	phba->sli4_hba.link_state.duplex = LPFC_ASYNC_LINK_DUPLEX_FULL;
	phba->sli4_hba.link_state.topology =
				bf_get(lpfc_acqe_fc_la_topology, acqe_fc);
	phba->sli4_hba.link_state.status =
				bf_get(lpfc_acqe_fc_la_att_type, acqe_fc);
	phba->sli4_hba.link_state.type =
				bf_get(lpfc_acqe_fc_la_port_type, acqe_fc);
	phba->sli4_hba.link_state.number =
				bf_get(lpfc_acqe_fc_la_port_number, acqe_fc);
	phba->sli4_hba.link_state.fault =
				bf_get(lpfc_acqe_link_fault, acqe_fc);
	phba->sli4_hba.link_state.logical_speed =
				bf_get(lpfc_acqe_fc_la_llink_spd, acqe_fc) * 10;
	lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
			"2896 Async FC event - Speed:%dGBaud Topology:x%x "
			"LA Type:x%x Port Type:%d Port Number:%d Logical speed:"
			"%dMbps Fault:%d\n",
			phba->sli4_hba.link_state.speed,
			phba->sli4_hba.link_state.topology,
			phba->sli4_hba.link_state.status,
			phba->sli4_hba.link_state.type,
			phba->sli4_hba.link_state.number,
			phba->sli4_hba.link_state.logical_speed,
			phba->sli4_hba.link_state.fault);
	pmb = (LPFC_MBOXQ_t *)mempool_alloc(phba->mbox_mem_pool, GFP_KERNEL);
	if (!pmb) {
		lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
				"2897 The mboxq allocation failed\n");
		return;
	}
	mp = kmalloc(sizeof(struct lpfc_dmabuf), GFP_KERNEL);
	if (!mp) {
		lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
				"2898 The lpfc_dmabuf allocation failed\n");
		goto out_free_pmb;
	}
	mp->virt = lpfc_mbuf_alloc(phba, 0, &mp->phys);
	if (!mp->virt) {
		lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
				"2899 The mbuf allocation failed\n");
		goto out_free_dmabuf;
	}

	/* Cleanup any outstanding ELS commands */
	lpfc_els_flush_all_cmd(phba);

	/* Block ELS IOCBs until we have done process link event */
	phba->sli.ring[LPFC_ELS_RING].flag |= LPFC_STOP_IOCB_EVENT;

	/* Update link event statistics */
	phba->sli.slistat.link_event++;

	/* Create lpfc_handle_latt mailbox command from link ACQE */
	lpfc_read_topology(phba, pmb, mp);
	pmb->mbox_cmpl = lpfc_mbx_cmpl_read_topology;
	pmb->vport = phba->pport;

	rc = lpfc_sli_issue_mbox(phba, pmb, MBX_NOWAIT);
	if (rc == MBX_NOT_FINISHED)
		goto out_free_dmabuf;
	return;

out_free_dmabuf:
	kfree(mp);
out_free_pmb:
	mempool_free(pmb, phba->mbox_mem_pool);
}

/**
 * lpfc_sli4_async_sli_evt - Process the asynchronous SLI link event
 * @phba: pointer to lpfc hba data structure.
 * @acqe_fc: pointer to the async SLI completion queue entry.
 *
 * This routine is to handle the SLI4 asynchronous SLI events.
 **/
static void
lpfc_sli4_async_sli_evt(struct lpfc_hba *phba, struct lpfc_acqe_sli *acqe_sli)
{
	char port_name;
	char message[128];
	uint8_t status;
	uint8_t evt_type;
	struct temp_event temp_event_data;
	struct lpfc_acqe_misconfigured_event *misconfigured;
	struct Scsi_Host  *shost;

	evt_type = bf_get(lpfc_trailer_type, acqe_sli);

	/* Special case Lancer */
	if (bf_get(lpfc_sli_intf_if_type, &phba->sli4_hba.sli_intf) !=
		 LPFC_SLI_INTF_IF_TYPE_2) {
		lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
				"2901 Async SLI event - Event Data1:x%08x Event Data2:"
				"x%08x SLI Event Type:%d\n",
				acqe_sli->event_data1, acqe_sli->event_data2,
				evt_type);
		return;
	}

	port_name = phba->Port[0];
	if (port_name == 0x00)
		port_name = '?'; /* get port name is empty */

	switch (evt_type) {
	case LPFC_SLI_EVENT_TYPE_OVER_TEMP:
		temp_event_data.event_type = FC_REG_TEMPERATURE_EVENT;
		temp_event_data.event_code = LPFC_THRESHOLD_TEMP;
		temp_event_data.data = (uint32_t)acqe_sli->event_data1;

		lpfc_printf_log(phba, KERN_WARNING, LOG_SLI,
				"3190 Over Temperature:%d Celsius- Port Name %c\n",
				acqe_sli->event_data1, port_name);

		shost = lpfc_shost_from_vport(phba->pport);
		fc_host_post_vendor_event(shost, fc_get_event_number(),
					  sizeof(temp_event_data),
					  (char *)&temp_event_data,
					  SCSI_NL_VID_TYPE_PCI
					  | PCI_VENDOR_ID_EMULEX);
		break;
	case LPFC_SLI_EVENT_TYPE_NORM_TEMP:
		temp_event_data.event_type = FC_REG_TEMPERATURE_EVENT;
		temp_event_data.event_code = LPFC_NORMAL_TEMP;
		temp_event_data.data = (uint32_t)acqe_sli->event_data1;

		lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
				"3191 Normal Temperature:%d Celsius - Port Name %c\n",
				acqe_sli->event_data1, port_name);

		shost = lpfc_shost_from_vport(phba->pport);
		fc_host_post_vendor_event(shost, fc_get_event_number(),
					  sizeof(temp_event_data),
					  (char *)&temp_event_data,
					  SCSI_NL_VID_TYPE_PCI
					  | PCI_VENDOR_ID_EMULEX);
		break;
	case LPFC_SLI_EVENT_TYPE_MISCONFIGURED:
		misconfigured = (struct lpfc_acqe_misconfigured_event *)
					&acqe_sli->event_data1;

		/* fetch the status for this port */
		switch (phba->sli4_hba.lnk_info.lnk_no) {
		case LPFC_LINK_NUMBER_0:
			status = bf_get(lpfc_sli_misconfigured_port0,
					&misconfigured->theEvent);
			break;
		case LPFC_LINK_NUMBER_1:
			status = bf_get(lpfc_sli_misconfigured_port1,
					&misconfigured->theEvent);
			break;
		case LPFC_LINK_NUMBER_2:
			status = bf_get(lpfc_sli_misconfigured_port2,
					&misconfigured->theEvent);
			break;
		case LPFC_LINK_NUMBER_3:
			status = bf_get(lpfc_sli_misconfigured_port3,
					&misconfigured->theEvent);
			break;
		default:
			status = ~LPFC_SLI_EVENT_STATUS_VALID;
			break;
		}

		switch (status) {
		case LPFC_SLI_EVENT_STATUS_VALID:
			return; /* no message if the sfp is okay */
		case LPFC_SLI_EVENT_STATUS_NOT_PRESENT:
			sprintf(message, "Optics faulted/incorrectly "
				"installed/not installed - Reseat optics, "
				"if issue not resolved, replace.");
			break;
		case LPFC_SLI_EVENT_STATUS_WRONG_TYPE:
			sprintf(message,
				"Optics of two types installed - Remove one "
				"optic or install matching pair of optics.");
			break;
		case LPFC_SLI_EVENT_STATUS_UNSUPPORTED:
			sprintf(message, "Incompatible optics - Replace with "
				"compatible optics for card to function.");
			break;
		default:
			/* firmware is reporting a status we don't know about */
			sprintf(message, "Unknown event status x%02x", status);
			break;
		}

		lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
				"3176 Misconfigured Physical Port - "
				"Port Name %c %s\n", port_name, message);
		break;
	case LPFC_SLI_EVENT_TYPE_REMOTE_DPORT:
		lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
				"3192 Remote DPort Test Initiated - "
				"Event Data1:x%08x Event Data2: x%08x\n",
				acqe_sli->event_data1, acqe_sli->event_data2);
		break;
	default:
		lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
				"3193 Async SLI event - Event Data1:x%08x Event Data2:"
				"x%08x SLI Event Type:%d\n",
				acqe_sli->event_data1, acqe_sli->event_data2,
				evt_type);
		break;
	}
}

/**
 * lpfc_sli4_perform_vport_cvl - Perform clear virtual link on a vport
 * @vport: pointer to vport data structure.
 *
 * This routine is to perform Clear Virtual Link (CVL) on a vport in
 * response to a CVL event.
 *
 * Return the pointer to the ndlp with the vport if successful, otherwise
 * return NULL.
 **/
static struct lpfc_nodelist *
lpfc_sli4_perform_vport_cvl(struct lpfc_vport *vport)
{
	struct lpfc_nodelist *ndlp;
	struct Scsi_Host *shost;
	struct lpfc_hba *phba;

	if (!vport)
		return NULL;
	phba = vport->phba;
	if (!phba)
		return NULL;
	ndlp = lpfc_findnode_did(vport, Fabric_DID);
	if (!ndlp) {
		/* Cannot find existing Fabric ndlp, so allocate a new one */
		ndlp = mempool_alloc(phba->nlp_mem_pool, GFP_KERNEL);
		if (!ndlp)
			return 0;
		lpfc_nlp_init(vport, ndlp, Fabric_DID);
		/* Set the node type */
		ndlp->nlp_type |= NLP_FABRIC;
		/* Put ndlp onto node list */
		lpfc_enqueue_node(vport, ndlp);
	} else if (!NLP_CHK_NODE_ACT(ndlp)) {
		/* re-setup ndlp without removing from node list */
		ndlp = lpfc_enable_node(vport, ndlp, NLP_STE_UNUSED_NODE);
		if (!ndlp)
			return 0;
	}
	if ((phba->pport->port_state < LPFC_FLOGI) &&
		(phba->pport->port_state != LPFC_VPORT_FAILED))
		return NULL;
	/* If virtual link is not yet instantiated ignore CVL */
	if ((vport != phba->pport) && (vport->port_state < LPFC_FDISC)
		&& (vport->port_state != LPFC_VPORT_FAILED))
		return NULL;
	shost = lpfc_shost_from_vport(vport);
	if (!shost)
		return NULL;
	lpfc_linkdown_port(vport);
	lpfc_cleanup_pending_mbox(vport);
	spin_lock_irq(shost->host_lock);
	vport->fc_flag |= FC_VPORT_CVL_RCVD;
	spin_unlock_irq(shost->host_lock);

	return ndlp;
}

/**
 * lpfc_sli4_perform_all_vport_cvl - Perform clear virtual link on all vports
 * @vport: pointer to lpfc hba data structure.
 *
 * This routine is to perform Clear Virtual Link (CVL) on all vports in
 * response to a FCF dead event.
 **/
static void
lpfc_sli4_perform_all_vport_cvl(struct lpfc_hba *phba)
{
	struct lpfc_vport **vports;
	int i;

	vports = lpfc_create_vport_work_array(phba);
	if (vports)
		for (i = 0; i <= phba->max_vports && vports[i] != NULL; i++)
			lpfc_sli4_perform_vport_cvl(vports[i]);
	lpfc_destroy_vport_work_array(phba, vports);
}

/**
 * lpfc_sli4_async_fip_evt - Process the asynchronous FCoE FIP event
 * @phba: pointer to lpfc hba data structure.
 * @acqe_link: pointer to the async fcoe completion queue entry.
 *
 * This routine is to handle the SLI4 asynchronous fcoe event.
 **/
static void
lpfc_sli4_async_fip_evt(struct lpfc_hba *phba,
			struct lpfc_acqe_fip *acqe_fip)
{
	uint8_t event_type = bf_get(lpfc_trailer_type, acqe_fip);
	int rc;
	struct lpfc_vport *vport;
	struct lpfc_nodelist *ndlp;
	struct Scsi_Host  *shost;
	int active_vlink_present;
	struct lpfc_vport **vports;
	int i;

	phba->fc_eventTag = acqe_fip->event_tag;
	phba->fcoe_eventtag = acqe_fip->event_tag;
	switch (event_type) {
	case LPFC_FIP_EVENT_TYPE_NEW_FCF:
	case LPFC_FIP_EVENT_TYPE_FCF_PARAM_MOD:
		if (event_type == LPFC_FIP_EVENT_TYPE_NEW_FCF)
			lpfc_printf_log(phba, KERN_ERR, LOG_FIP |
					LOG_DISCOVERY,
					"2546 New FCF event, evt_tag:x%x, "
					"index:x%x\n",
					acqe_fip->event_tag,
					acqe_fip->index);
		else
			lpfc_printf_log(phba, KERN_WARNING, LOG_FIP |
					LOG_DISCOVERY,
					"2788 FCF param modified event, "
					"evt_tag:x%x, index:x%x\n",
					acqe_fip->event_tag,
					acqe_fip->index);
		if (phba->fcf.fcf_flag & FCF_DISCOVERY) {
			/*
			 * During period of FCF discovery, read the FCF
			 * table record indexed by the event to update
			 * FCF roundrobin failover eligible FCF bmask.
			 */
			lpfc_printf_log(phba, KERN_INFO, LOG_FIP |
					LOG_DISCOVERY,
					"2779 Read FCF (x%x) for updating "
					"roundrobin FCF failover bmask\n",
					acqe_fip->index);
			rc = lpfc_sli4_read_fcf_rec(phba, acqe_fip->index);
		}

		/* If the FCF discovery is in progress, do nothing. */
		spin_lock_irq(&phba->hbalock);
		if (phba->hba_flag & FCF_TS_INPROG) {
			spin_unlock_irq(&phba->hbalock);
			break;
		}
		/* If fast FCF failover rescan event is pending, do nothing */
		if (phba->fcf.fcf_flag & FCF_REDISC_EVT) {
			spin_unlock_irq(&phba->hbalock);
			break;
		}

		/* If the FCF has been in discovered state, do nothing. */
		if (phba->fcf.fcf_flag & FCF_SCAN_DONE) {
			spin_unlock_irq(&phba->hbalock);
			break;
		}
		spin_unlock_irq(&phba->hbalock);

		/* Otherwise, scan the entire FCF table and re-discover SAN */
		lpfc_printf_log(phba, KERN_INFO, LOG_FIP | LOG_DISCOVERY,
				"2770 Start FCF table scan per async FCF "
				"event, evt_tag:x%x, index:x%x\n",
				acqe_fip->event_tag, acqe_fip->index);
		rc = lpfc_sli4_fcf_scan_read_fcf_rec(phba,
						     LPFC_FCOE_FCF_GET_FIRST);
		if (rc)
			lpfc_printf_log(phba, KERN_ERR, LOG_FIP | LOG_DISCOVERY,
					"2547 Issue FCF scan read FCF mailbox "
					"command failed (x%x)\n", rc);
		break;

	case LPFC_FIP_EVENT_TYPE_FCF_TABLE_FULL:
		lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
			"2548 FCF Table full count 0x%x tag 0x%x\n",
			bf_get(lpfc_acqe_fip_fcf_count, acqe_fip),
			acqe_fip->event_tag);
		break;

	case LPFC_FIP_EVENT_TYPE_FCF_DEAD:
		phba->fcoe_cvl_eventtag = acqe_fip->event_tag;
		lpfc_printf_log(phba, KERN_ERR, LOG_FIP | LOG_DISCOVERY,
			"2549 FCF (x%x) disconnected from network, "
			"tag:x%x\n", acqe_fip->index, acqe_fip->event_tag);
		/*
		 * If we are in the middle of FCF failover process, clear
		 * the corresponding FCF bit in the roundrobin bitmap.
		 */
		spin_lock_irq(&phba->hbalock);
		if (phba->fcf.fcf_flag & FCF_DISCOVERY) {
			spin_unlock_irq(&phba->hbalock);
			/* Update FLOGI FCF failover eligible FCF bmask */
			lpfc_sli4_fcf_rr_index_clear(phba, acqe_fip->index);
			break;
		}
		spin_unlock_irq(&phba->hbalock);

		/* If the event is not for currently used fcf do nothing */
		if (phba->fcf.current_rec.fcf_indx != acqe_fip->index)
			break;

		/*
		 * Otherwise, request the port to rediscover the entire FCF
		 * table for a fast recovery from case that the current FCF
		 * is no longer valid as we are not in the middle of FCF
		 * failover process already.
		 */
		spin_lock_irq(&phba->hbalock);
		/* Mark the fast failover process in progress */
		phba->fcf.fcf_flag |= FCF_DEAD_DISC;
		spin_unlock_irq(&phba->hbalock);

		lpfc_printf_log(phba, KERN_INFO, LOG_FIP | LOG_DISCOVERY,
				"2771 Start FCF fast failover process due to "
				"FCF DEAD event: evt_tag:x%x, fcf_index:x%x "
				"\n", acqe_fip->event_tag, acqe_fip->index);
		rc = lpfc_sli4_redisc_fcf_table(phba);
		if (rc) {
			lpfc_printf_log(phba, KERN_ERR, LOG_FIP |
					LOG_DISCOVERY,
					"2772 Issue FCF rediscover mabilbox "
					"command failed, fail through to FCF "
					"dead event\n");
			spin_lock_irq(&phba->hbalock);
			phba->fcf.fcf_flag &= ~FCF_DEAD_DISC;
			spin_unlock_irq(&phba->hbalock);
			/*
			 * Last resort will fail over by treating this
			 * as a link down to FCF registration.
			 */
			lpfc_sli4_fcf_dead_failthrough(phba);
		} else {
			/* Reset FCF roundrobin bmask for new discovery */
			lpfc_sli4_clear_fcf_rr_bmask(phba);
			/*
			 * Handling fast FCF failover to a DEAD FCF event is
			 * considered equalivant to receiving CVL to all vports.
			 */
			lpfc_sli4_perform_all_vport_cvl(phba);
		}
		break;
	case LPFC_FIP_EVENT_TYPE_CVL:
		phba->fcoe_cvl_eventtag = acqe_fip->event_tag;
		lpfc_printf_log(phba, KERN_ERR, LOG_FIP | LOG_DISCOVERY,
			"2718 Clear Virtual Link Received for VPI 0x%x"
			" tag 0x%x\n", acqe_fip->index, acqe_fip->event_tag);

		vport = lpfc_find_vport_by_vpid(phba,
						acqe_fip->index);
		ndlp = lpfc_sli4_perform_vport_cvl(vport);
		if (!ndlp)
			break;
		active_vlink_present = 0;

		vports = lpfc_create_vport_work_array(phba);
		if (vports) {
			for (i = 0; i <= phba->max_vports && vports[i] != NULL;
					i++) {
				if ((!(vports[i]->fc_flag &
					FC_VPORT_CVL_RCVD)) &&
					(vports[i]->port_state > LPFC_FDISC)) {
					active_vlink_present = 1;
					break;
				}
			}
			lpfc_destroy_vport_work_array(phba, vports);
		}

		if (active_vlink_present) {
			/*
			 * If there are other active VLinks present,
			 * re-instantiate the Vlink using FDISC.
			 */
			mod_timer(&ndlp->nlp_delayfunc,
				  jiffies + msecs_to_jiffies(1000));
			shost = lpfc_shost_from_vport(vport);
			spin_lock_irq(shost->host_lock);
			ndlp->nlp_flag |= NLP_DELAY_TMO;
			spin_unlock_irq(shost->host_lock);
			ndlp->nlp_last_elscmd = ELS_CMD_FDISC;
			vport->port_state = LPFC_FDISC;
		} else {
			/*
			 * Otherwise, we request port to rediscover
			 * the entire FCF table for a fast recovery
			 * from possible case that the current FCF
			 * is no longer valid if we are not already
			 * in the FCF failover process.
			 */
			spin_lock_irq(&phba->hbalock);
			if (phba->fcf.fcf_flag & FCF_DISCOVERY) {
				spin_unlock_irq(&phba->hbalock);
				break;
			}
			/* Mark the fast failover process in progress */
			phba->fcf.fcf_flag |= FCF_ACVL_DISC;
			spin_unlock_irq(&phba->hbalock);
			lpfc_printf_log(phba, KERN_INFO, LOG_FIP |
					LOG_DISCOVERY,
					"2773 Start FCF failover per CVL, "
					"evt_tag:x%x\n", acqe_fip->event_tag);
			rc = lpfc_sli4_redisc_fcf_table(phba);
			if (rc) {
				lpfc_printf_log(phba, KERN_ERR, LOG_FIP |
						LOG_DISCOVERY,
						"2774 Issue FCF rediscover "
						"mabilbox command failed, "
						"through to CVL event\n");
				spin_lock_irq(&phba->hbalock);
				phba->fcf.fcf_flag &= ~FCF_ACVL_DISC;
				spin_unlock_irq(&phba->hbalock);
				/*
				 * Last resort will be re-try on the
				 * the current registered FCF entry.
				 */
				lpfc_retry_pport_discovery(phba);
			} else
				/*
				 * Reset FCF roundrobin bmask for new
				 * discovery.
				 */
				lpfc_sli4_clear_fcf_rr_bmask(phba);
		}
		break;
	default:
		lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
			"0288 Unknown FCoE event type 0x%x event tag "
			"0x%x\n", event_type, acqe_fip->event_tag);
		break;
	}
}

/**
 * lpfc_sli4_async_dcbx_evt - Process the asynchronous dcbx event
 * @phba: pointer to lpfc hba data structure.
 * @acqe_link: pointer to the async dcbx completion queue entry.
 *
 * This routine is to handle the SLI4 asynchronous dcbx event.
 **/
static void
lpfc_sli4_async_dcbx_evt(struct lpfc_hba *phba,
			 struct lpfc_acqe_dcbx *acqe_dcbx)
{
	phba->fc_eventTag = acqe_dcbx->event_tag;
	lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
			"0290 The SLI4 DCBX asynchronous event is not "
			"handled yet\n");
}

/**
 * lpfc_sli4_async_grp5_evt - Process the asynchronous group5 event
 * @phba: pointer to lpfc hba data structure.
 * @acqe_link: pointer to the async grp5 completion queue entry.
 *
 * This routine is to handle the SLI4 asynchronous grp5 event. A grp5 event
 * is an asynchronous notified of a logical link speed change.  The Port
 * reports the logical link speed in units of 10Mbps.
 **/
static void
lpfc_sli4_async_grp5_evt(struct lpfc_hba *phba,
			 struct lpfc_acqe_grp5 *acqe_grp5)
{
	uint16_t prev_ll_spd;

	phba->fc_eventTag = acqe_grp5->event_tag;
	phba->fcoe_eventtag = acqe_grp5->event_tag;
	prev_ll_spd = phba->sli4_hba.link_state.logical_speed;
	phba->sli4_hba.link_state.logical_speed =
		(bf_get(lpfc_acqe_grp5_llink_spd, acqe_grp5)) * 10;
	lpfc_printf_log(phba, KERN_INFO, LOG_SLI,
			"2789 GRP5 Async Event: Updating logical link speed "
			"from %dMbps to %dMbps\n", prev_ll_spd,
			phba->sli4_hba.link_state.logical_speed);
}

/**
 * lpfc_sli4_async_event_proc - Process all the pending asynchronous event
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked by the worker thread to process all the pending
 * SLI4 asynchronous events.
 **/
void lpfc_sli4_async_event_proc(struct lpfc_hba *phba)
{
	struct lpfc_cq_event *cq_event;

	/* First, declare the async event has been handled */
	spin_lock_irq(&phba->hbalock);
	phba->hba_flag &= ~ASYNC_EVENT;
	spin_unlock_irq(&phba->hbalock);
	/* Now, handle all the async events */
	while (!list_empty(&phba->sli4_hba.sp_asynce_work_queue)) {
		/* Get the first event from the head of the event queue */
		spin_lock_irq(&phba->hbalock);
		list_remove_head(&phba->sli4_hba.sp_asynce_work_queue,
				 cq_event, struct lpfc_cq_event, list);
		spin_unlock_irq(&phba->hbalock);
		/* Process the asynchronous event */
		switch (bf_get(lpfc_trailer_code, &cq_event->cqe.mcqe_cmpl)) {
		case LPFC_TRAILER_CODE_LINK:
			lpfc_sli4_async_link_evt(phba,
						 &cq_event->cqe.acqe_link);
			break;
		case LPFC_TRAILER_CODE_FCOE:
			lpfc_sli4_async_fip_evt(phba, &cq_event->cqe.acqe_fip);
			break;
		case LPFC_TRAILER_CODE_DCBX:
			lpfc_sli4_async_dcbx_evt(phba,
						 &cq_event->cqe.acqe_dcbx);
			break;
		case LPFC_TRAILER_CODE_GRP5:
			lpfc_sli4_async_grp5_evt(phba,
						 &cq_event->cqe.acqe_grp5);
			break;
		case LPFC_TRAILER_CODE_FC:
			lpfc_sli4_async_fc_evt(phba, &cq_event->cqe.acqe_fc);
			break;
		case LPFC_TRAILER_CODE_SLI:
			lpfc_sli4_async_sli_evt(phba, &cq_event->cqe.acqe_sli);
			break;
		default:
			lpfc_printf_log(phba, KERN_ERR, LOG_SLI,
					"1804 Invalid asynchrous event code: "
					"x%x\n", bf_get(lpfc_trailer_code,
					&cq_event->cqe.mcqe_cmpl));
			break;
		}
		/* Free the completion event processed to the free pool */
		lpfc_sli4_cq_event_release(phba, cq_event);
	}
}

/**
 * lpfc_sli4_fcf_redisc_event_proc - Process fcf table rediscovery event
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked by the worker thread to process FCF table
 * rediscovery pending completion event.
 **/
void lpfc_sli4_fcf_redisc_event_proc(struct lpfc_hba *phba)
{
	int rc;

	spin_lock_irq(&phba->hbalock);
	/* Clear FCF rediscovery timeout event */
	phba->fcf.fcf_flag &= ~FCF_REDISC_EVT;
	/* Clear driver fast failover FCF record flag */
	phba->fcf.failover_rec.flag = 0;
	/* Set state for FCF fast failover */
	phba->fcf.fcf_flag |= FCF_REDISC_FOV;
	spin_unlock_irq(&phba->hbalock);

	/* Scan FCF table from the first entry to re-discover SAN */
	lpfc_printf_log(phba, KERN_INFO, LOG_FIP | LOG_DISCOVERY,
			"2777 Start post-quiescent FCF table scan\n");
	rc = lpfc_sli4_fcf_scan_read_fcf_rec(phba, LPFC_FCOE_FCF_GET_FIRST);
	if (rc)
		lpfc_printf_log(phba, KERN_ERR, LOG_FIP | LOG_DISCOVERY,
				"2747 Issue FCF scan read FCF mailbox "
				"command failed 0x%x\n", rc);
}

/**
 * lpfc_api_table_setup - Set up per hba pci-device group func api jump table
 * @phba: pointer to lpfc hba data structure.
 * @dev_grp: The HBA PCI-Device group number.
 *
 * This routine is invoked to set up the per HBA PCI-Device group function
 * API jump table entries.
 *
 * Return: 0 if success, otherwise -ENODEV
 **/
int
lpfc_api_table_setup(struct lpfc_hba *phba, uint8_t dev_grp)
{
	int rc;

	/* Set up lpfc PCI-device group */
	phba->pci_dev_grp = dev_grp;

	/* The LPFC_PCI_DEV_OC uses SLI4 */
	if (dev_grp == LPFC_PCI_DEV_OC)
		phba->sli_rev = LPFC_SLI_REV4;

	/* Set up device INIT API function jump table */
	rc = lpfc_init_api_table_setup(phba, dev_grp);
	if (rc)
		return -ENODEV;
	/* Set up SCSI API function jump table */
	rc = lpfc_scsi_api_table_setup(phba, dev_grp);
	if (rc)
		return -ENODEV;
	/* Set up SLI API function jump table */
	rc = lpfc_sli_api_table_setup(phba, dev_grp);
	if (rc)
		return -ENODEV;
	/* Set up MBOX API function jump table */
	rc = lpfc_mbox_api_table_setup(phba, dev_grp);
	if (rc)
		return -ENODEV;

	return 0;
}

/**
 * lpfc_log_intr_mode - Log the active interrupt mode
 * @phba: pointer to lpfc hba data structure.
 * @intr_mode: active interrupt mode adopted.
 *
 * This routine it invoked to log the currently used active interrupt mode
 * to the device.
 **/
static void lpfc_log_intr_mode(struct lpfc_hba *phba, uint32_t intr_mode)
{
	switch (intr_mode) {
	case 0:
		lpfc_printf_log(phba, KERN_INFO, LOG_INIT,
				"0470 Enable INTx interrupt mode.\n");
		break;
	case 1:
		lpfc_printf_log(phba, KERN_INFO, LOG_INIT,
				"0481 Enabled MSI interrupt mode.\n");
		break;
	case 2:
		lpfc_printf_log(phba, KERN_INFO, LOG_INIT,
				"0480 Enabled MSI-X interrupt mode.\n");
		break;
	default:
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"0482 Illegal interrupt mode.\n");
		break;
	}
	return;
}

/**
 * lpfc_enable_pci_dev - Enable a generic PCI device.
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked to enable the PCI device that is common to all
 * PCI devices.
 *
 * Return codes
 * 	0 - successful
 * 	other values - error
 **/
static int
lpfc_enable_pci_dev(struct lpfc_hba *phba)
{
	struct pci_dev *pdev;
	int bars = 0;

	/* Obtain PCI device reference */
	if (!phba->pcidev)
		goto out_error;
	else
		pdev = phba->pcidev;
	/* Select PCI BARs */
	bars = pci_select_bars(pdev, IORESOURCE_MEM);
	/* Enable PCI device */
	if (pci_enable_device_mem(pdev))
		goto out_error;
	/* Request PCI resource for the device */
	if (pci_request_selected_regions(pdev, bars, LPFC_DRIVER_NAME))
		goto out_disable_device;
	/* Set up device as PCI master and save state for EEH */
	pci_set_master(pdev);
	pci_try_set_mwi(pdev);
	pci_save_state(pdev);

	/* PCIe EEH recovery on powerpc platforms needs fundamental reset */
	if (pci_is_pcie(pdev))
		pdev->needs_freset = 1;

	return 0;

out_disable_device:
	pci_disable_device(pdev);
out_error:
	lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
			"1401 Failed to enable pci device, bars:x%x\n", bars);
	return -ENODEV;
}

/**
 * lpfc_disable_pci_dev - Disable a generic PCI device.
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked to disable the PCI device that is common to all
 * PCI devices.
 **/
static void
lpfc_disable_pci_dev(struct lpfc_hba *phba)
{
	struct pci_dev *pdev;
	int bars;

	/* Obtain PCI device reference */
	if (!phba->pcidev)
		return;
	else
		pdev = phba->pcidev;
	/* Select PCI BARs */
	bars = pci_select_bars(pdev, IORESOURCE_MEM);
	/* Release PCI resource and disable PCI device */
	pci_release_selected_regions(pdev, bars);
	pci_disable_device(pdev);

	return;
}

/**
 * lpfc_reset_hba - Reset a hba
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked to reset a hba device. It brings the HBA
 * offline, performs a board restart, and then brings the board back
 * online. The lpfc_offline calls lpfc_sli_hba_down which will clean up
 * on outstanding mailbox commands.
 **/
void
lpfc_reset_hba(struct lpfc_hba *phba)
{
	/* If resets are disabled then set error state and return. */
	if (!phba->cfg_enable_hba_reset) {
		phba->link_state = LPFC_HBA_ERROR;
		return;
	}
	if (phba->sli.sli_flag & LPFC_SLI_ACTIVE)
		lpfc_offline_prep(phba, LPFC_MBX_WAIT);
	else
		lpfc_offline_prep(phba, LPFC_MBX_NO_WAIT);
	lpfc_offline(phba);
	lpfc_sli_brdrestart(phba);
	lpfc_online(phba);
	lpfc_unblock_mgmt_io(phba);
}

/**
 * lpfc_sli_sriov_nr_virtfn_get - Get the number of sr-iov virtual functions
 * @phba: pointer to lpfc hba data structure.
 *
 * This function enables the PCI SR-IOV virtual functions to a physical
 * function. It invokes the PCI SR-IOV api with the @nr_vfn provided to
 * enable the number of virtual functions to the physical function. As
 * not all devices support SR-IOV, the return code from the pci_enable_sriov()
 * API call does not considered as an error condition for most of the device.
 **/
uint16_t
lpfc_sli_sriov_nr_virtfn_get(struct lpfc_hba *phba)
{
	struct pci_dev *pdev = phba->pcidev;
	uint16_t nr_virtfn;
	int pos;

	pos = pci_find_ext_capability(pdev, PCI_EXT_CAP_ID_SRIOV);
	if (pos == 0)
		return 0;

	pci_read_config_word(pdev, pos + PCI_SRIOV_TOTAL_VF, &nr_virtfn);
	return nr_virtfn;
}

/**
 * lpfc_sli_probe_sriov_nr_virtfn - Enable a number of sr-iov virtual functions
 * @phba: pointer to lpfc hba data structure.
 * @nr_vfn: number of virtual functions to be enabled.
 *
 * This function enables the PCI SR-IOV virtual functions to a physical
 * function. It invokes the PCI SR-IOV api with the @nr_vfn provided to
 * enable the number of virtual functions to the physical function. As
 * not all devices support SR-IOV, the return code from the pci_enable_sriov()
 * API call does not considered as an error condition for most of the device.
 **/
int
lpfc_sli_probe_sriov_nr_virtfn(struct lpfc_hba *phba, int nr_vfn)
{
	struct pci_dev *pdev = phba->pcidev;
	uint16_t max_nr_vfn;
	int rc;

	max_nr_vfn = lpfc_sli_sriov_nr_virtfn_get(phba);
	if (nr_vfn > max_nr_vfn) {
		lpfc_printf_log(phba, KERN_ERR, LOG_INIT,
				"3057 Requested vfs (%d) greater than "
				"supported vfs (%d)", nr_vfn, max_nr_vfn);
		return -EINVAL;
	}

	rc = pci_enable_sriov(pdev, nr_vfn);
	if (rc) {
		lpfc_printf_log(phba, KERN_WARNING, LOG_INIT,
				"2806 Failed to enable sriov on this device "
				"with vfn number nr_vf:%d, rc:%d\n",
				nr_vfn, rc);
	} else
		lpfc_printf_log(phba, KERN_WARNING, LOG_INIT,
				"2807 Successful enable sriov on this device "
				"with vfn number nr_vf:%d\n", nr_vfn);
	return rc;
}

/**
 * lpfc_sli_driver_resource_setup - Setup driver internal resources for SLI3 dev.
 * @phba: pointer to lpfc hba data structure.
 *
 * This routine is invoked to set up the driver internal resources specific to
 * support the SLI-3 HBA device it attached to.
 *
 * Return codes
 * 	0 - successful
 * 	other values - error
 **/
static int
lpfc_sli_driver_resource_setup(struct lpfc_hba *phba)
{
	struct lpfc_sli *psli;
	int rc;

	/*
	 * Initialize timers used by driver
	 */

	/* Heartbeat timer */
	init_timer(&phba->hb_tmofunc);
	phba->hb_tmofunc.function = lpfc_hb_timeout;
	phba->hb_tmofunc.data = (unsigned long)phba;

	psli = &phba->sli;
	/* MBOX heartbeat timer */
	init_timer(&psli->mbox_tmo);
	psli->mbox_tmo.function = lpfc_mbox_timeout;
	psli->mbox_tmo.data = (unsigned long) phba;
	/* FCP polling mode timer */
	init_timer(&phba->fcp_po