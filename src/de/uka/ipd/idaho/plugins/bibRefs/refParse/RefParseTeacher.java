/* RefParse, the algorithm for parsing lists of bibliographic references.
 * Copyright (C) 2011-2013 ViBRANT (FP7/2007-2013, GA 261532), by G. Sautter
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */
package de.uka.ipd.idaho.plugins.bibRefs.refParse;

import java.util.Properties;

import de.uka.ipd.idaho.gamta.MutableAnnotation;

/**
 * @author sautter
 *
 */
public class RefParseTeacher extends RefParseAnalyzer {
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.plugins.bibliographicReferences.RefParseAnalyzer#processBibRefs(de.uka.ipd.idaho.gamta.MutableAnnotation, de.uka.ipd.idaho.gamta.MutableAnnotation[], java.util.Properties)
	 */
	protected void processBibRefs(MutableAnnotation data, MutableAnnotation[] bibRefAnnots, Properties parameters) {
		for (int r = 0; r < bibRefAnnots.length; r++)
			this.refParse.learnDetails(bibRefAnnots[r]);
	}
}
